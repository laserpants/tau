{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Expr.Patterns where

import Control.Applicative ((<|>))
import Control.Arrow
import Control.Monad
import Control.Monad.Extra (maybeM, anyM)
import Control.Monad.Free 
import Control.Monad.Trans.Free (FreeT(..))
import Control.Monad.Reader
import Control.Monad.Supply 
import Control.Monad.Except
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.Tuple.Extra (fst3, snd3, thd3)
import Data.List.Extra (groupSortOn, groupBy, sortOn)
import Data.Maybe (fromJust, fromMaybe, maybeToList)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (fst3, thd3)
import Debug.Trace
import Tau.Env
import Tau.Expr
import Tau.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Control.Monad.Free as Monad
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

newtype Simplify a = Simplify { unSimplify :: ExceptT String (Supply Name) a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadSupply Name
    , MonadError String )

runSimplify :: Simplify a -> Either String a
runSimplify = unSimplify 
    >>> runExceptT
    >>> flip evalSupply (nameSupply "$")
    >>> fromMaybe (throwError "Error") -- (throwError ImplementationError)

data MatchExprF t a
    = Match [Expr t (Prep t) Name] [Clause (Pattern t) (Expr t (Prep t) Name)] a
    | Fail
    deriving (Show, Eq, Functor, Foldable, Traversable)

type MatchExpr t = Fix (MatchExprF t)

data TranslatedF m t a
    = Wrap (m a)
    | SimpleMatch a [(Prep t, a)]
    | If a a a
    | Expr (Expr t (Prep t) Name)
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Translated m t = Fix (TranslatedF m t)

deriveShow1 ''MatchExprF
deriveEq1   ''MatchExprF

deriveShow1 ''TranslatedF
deriveEq1   ''TranslatedF

class Boolean t where
    boolean :: t

instance Boolean () where
    boolean = ()

instance Boolean Type where
    boolean = tBool

-- ??? TODO
instance Boolean (Type, [a]) where
    boolean = (tBool, [])

simplified 
  :: (Boolean t, Show t) 
  => Expr t (Pattern t) (Pattern t) 
  -> Either String (Expr t (Prep t) Name)
simplified = runSimplify . simplify

simplify 
  :: (Boolean t, Show t) 
  => Expr t (Pattern t) (Pattern t) 
  -> Simplify (Expr t (Prep t) Name)
simplify = cata $ \case
    EVar t var     -> pure (varExpr t var)
    ECon t con exs -> conExpr t con <$> sequence exs
    ELit t lit     -> pure (litExpr t lit)
    EApp t exs     -> appExpr t <$> sequence exs

    --
    --  Let-expressions can only bind to simple variables (formal parameters)
    --
    ELet t (Fix (PVar _ var)) e1 e2 -> 
        letExpr t var <$> e1 <*> e2

    --
    --  The same restriction applies to lambdas
    --
    ELam t (Fix (PVar _ var)) e1 -> 
        lamExpr t var <$> e1 

    --
    --  Expressions like \5 => ..., let 5 = ..., or let _ = ... are not allowed
    --
    ELam _ (Fix PLit{}) _   -> throwError "Pattern not allowed"
    ELet _ (Fix PLit{}) _ _ -> throwError "Pattern not allowed"
    ELam _ (Fix PAny{}) _   -> throwError "Pattern not allowed"
    ELet _ (Fix PAny{}) _ _ -> throwError "Pattern not allowed"

    --
    --  Expressions like let C x = y in f x
    --  get translated to: match y with | C x => f x
    --
    ELet _ rep e1 e2 -> do
        expr <- e1
        body <- e2
        compile [expr] [Clause [rep] [] body]

    --
    --  Lambda expressions like \(C x) => f x
    --  get translated to \$z => match $z with | C x => f x in $z
    --  where $z is a fresh variable
    --
    ELam t rep e1 -> do
        fresh <- supply
        body <- e1
        expr <- compile [varExpr t fresh] [Clause [rep] [] body]
        pure (lamExpr t fresh expr)

    EIf t cond e1 e2 ->
        ifExpr t <$> cond <*> e1 <*> e2

    EMat t exs eqs -> do
        join (compile <$> sequence exs <*> traverse sequence eqs)

    EOp t op ->
        simplifyOp t op

    ERec t fields -> do
        recExpr t <$> traverse sequence fields

simplifyOp :: t -> Op (Simplify (Expr t p q)) -> Simplify (Expr t p q)
simplifyOp t (OEq  a b) = eqOp  t <$> a <*> b
simplifyOp t (OAnd a b) = andOp t <$> a <*> b
simplifyOp t (OOr  a b) = orOp  t <$> a <*> b

flatten 
  :: (Boolean t, Show t) 
  => Clause (Pattern t) (Expr t p q) 
  -> Clause (Pattern t) (Expr t p q)
flatten (Clause ps exs e) = Clause qs (exs <> exs1) e where
    (qs, exs1) = fmap concat (unzip (fmap fn ps))
    fn pat = fromJust (evalSupply (runWriterT (cata alg pat)) (nameSupply "$"))
    alg = \case
        PAny t -> 
            pure (varPat t "$_")

        PLit t lit -> do
            var <- supply
            tell [eqOp boolean (varExpr t var) (litExpr t lit)]
            pure (varPat t var)

        PRec t fields -> do
            let info = sortedFields fields
            ps <- traverse thd3 info
            pure (conPat t ("{" <> Text.intercalate "," (snd3 <$> info) <> "}") ps)

        pat ->
            embed <$> sequence pat

compile 
  :: (Boolean t, Show t) 
  => [Expr t (Prep t) Name]
  -> [Clause (Pattern t) (Expr t (Prep t) Name)]
  -> Simplify (Expr t (Prep t) Name)
compile es qs = 
    Match es (flatten <$> qs) (embed Fail)
      & embed
      & translate  
      & collapse 
  where
    collapse 
      :: Translated Simplify t 
      -> Simplify (Expr t (Prep t) Name)
    collapse = cata $ \case
        Wrap a -> join a
        Expr a -> pure a
        If cond tr fl -> 
            ifExpr <$> (getTag <$> tr) 
                   <*> cond 
                   <*> tr 
                   <*> fl
        SimpleMatch ex css -> do
            expr <- ex
            (eqs, ts) <- unzip <$> traverse fn css
            pure (matExpr (head ts) [expr] eqs)
          where
            fn (rep, ex1) = do
                expr <- ex1
                pure ( Clause [rep] [] expr
                     , getTag expr )

translate :: (Show t) => MatchExpr t -> Translated Simplify t
translate = futu $ project >>> \case
    Fail ->
        Wrap (throwError "Fail")

    Match [] [] c ->
        Wrap (pure (Pure c))

    Match [] (Clause [] [] e:_) _ ->
        Expr e

    Match [] (Clause [] exs e:qs) c ->
        If (Free (Expr (foldr1 (\a -> andOp (getTag a) a) exs))) 
           (Free (Expr e)) 
           (Pure (embed (Match [] qs c)))

    Match (u:us) qs c ->
        Wrap $ case equationGroups qs of
            [VarTag eqs] -> 
                pure (Pure (embed (Match us (runSubst <$> eqs) c)))
                  where
                    runSubst (Clause (Fix (PVar _ name):ps) exs e) = 
                        substitute name u <$> Clause ps exs e

            [ConTag eqs] -> do
                Free . SimpleMatch (Free (Expr u)) <$> traverse toSimpleMatch (conGroups eqs)
                  where
                    toSimpleMatch (ConGroup t con ps eqs) = do
                        vars <- supplies (length ps)
                        pure ( RCon t con vars
                             , Pure (embed (Match (combine ps vars <> us) eqs c)) )

                    combine ps vs = 
                        uncurry (varExpr . getTag) <$> zip ps vs

            mixed -> 
                pure (Pure (embed (foldr fn (project c) (getEqs <$> mixed))))
              where
                getEqs (ConTag a) = a
                getEqs (VarTag a) = a

                fn eqs a = Match (u:us) eqs (embed a)

--- 
--- 

substitute 
  :: Name 
  -> Expr t (Prep t) Name 
  -> Expr t (Prep t) Name 
  -> Expr t (Prep t) Name
substitute name subst = para $ \case
    ELet t pat (_, e1) e2 -> letExpr t pat e1 e2'
      where 
        e2' | name == pat = fst e2
            | otherwise   = snd e2

    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EMat t exs eqs -> matExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq eq@(Clause ps _ _) 
            | name `elem` free ps = fst <$> eq
            | otherwise           = snd <$> eq

    expr -> snd <$> expr & \case
        EVar t var 
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e

        --ECon t con exs  -> conExpr t con exs
        --ELit t lit      -> litExpr t lit
        --EApp t exs      -> appExpr t exs
        --EIf  t c e1 e2  -> ifExpr  t c e1 e2
        --EOp  t op       -> substOp t op
--  where
--    substOp t = \case
--        OEq  a b -> eqOp  t a b
--        OAnd a b -> andOp t a b
--        OOr  a b -> orOp  t a b

data Tagged a = ConTag a | VarTag a
    deriving (Show, Eq, Ord)

taggedEq :: Clause (Pattern t) a -> Tagged (Clause (Pattern t) a)
taggedEq eq@(Clause ps _ _) = 
    case project <$> ps of
        PCon{}:_ -> ConTag eq
        _        -> VarTag eq

equationGroups :: [Clause (Pattern t) a] -> [Tagged [Clause (Pattern t) a]]
equationGroups = cata alg . fmap taggedEq where
    alg Nil = []
    alg (Cons (ConTag e) (ConTag es:ts)) = ConTag (e:es):ts
    alg (Cons (VarTag e) (VarTag es:ts)) = VarTag (e:es):ts
    alg (Cons (ConTag e) ts) = ConTag [e]:ts
    alg (Cons (VarTag e) ts) = VarTag [e]:ts

data ConGroup t a = ConGroup t Name [Pattern t] [Clause (Pattern t) a]
    deriving (Show, Eq)

conGroups :: [Clause (Pattern t) a] -> [ConGroup t a]
conGroups =
    concatMap conGroup
      . groupSortOn (fst3 . snd)
      . concatMap expanded
  where
    conGroup all@((t, (con, ps, _)):_) = 
        [ConGroup t con ps (thd3 . snd <$> all)]
    conGroup [] = 
        []
    expanded (Clause (Fix (PCon t con ps):qs) exs e) =
        [(t, (con, ps, Clause (ps <> qs) exs e))]

patternVars :: Pattern t -> [(Name, t)]
patternVars = cata $ \case
    PVar t var    -> [(var, t)]
    PCon _ con rs -> concat rs
    PLit _ lit    -> []
    PAny _        -> []

-- ****************************************************************************
-- ****************************************************************************
-- ****************************************************************************
-- ****************************************************************************

specialized :: Name -> [t] -> [[Pattern t]] -> [[Pattern t]]
specialized name ts = concatMap rec where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ name' ps'
                | name' == name -> [ps' <> ps]
                | otherwise     -> []
            _ ->
                [(anyPat <$> ts) <> ps]

defaultMatrix :: [[Pattern t]] -> [[Pattern t]]
defaultMatrix = concatMap $ \(p:ps) ->
    case project p of
        PCon{} -> []
        PLit{} -> []
        _      -> [ps]

type ConstructorEnv = Env (Set Name)

headCons :: (MonadReader ConstructorEnv m) => [[Pattern t]] -> m [(Name, [Pattern t])]
headCons = fmap concat . traverse fun where
    fun [] = error "Implementation error (headCons)"
    fun ps = pure $ case unfix (head ps) of
        PLit _ lit       -> [(prim lit, [])]
        PCon _ name rs   -> [(name, rs)]
--      PRec fields      -> let n = length fields in [(recordCon n, 2 * n)]
        _                -> []
    prim (LBool True)  = "$True"
    prim (LBool False) = "$False"
    prim LUnit         = "$()"
    prim LInt{}        = "$Int"
    prim LInteger{}    = "$Integer"
    prim LFloat{}      = "$Float"
    prim LChar{}       = "$Char"
    prim LString{}     = "$String"

constructorEnv :: [(Name, [Name])] -> ConstructorEnv
constructorEnv = Env.fromList . fmap (Set.fromList <$>)

useful :: (MonadReader ConstructorEnv m) => [[Pattern t]] -> [Pattern t] -> m Bool
useful [] _ = pure True        -- Zero rows (0x0 matrix)
useful px@(ps:_) qs =
    case (qs, length ps) of
        (_, 0)  -> pure False  -- One or more rows but no columns
        ([], _) -> error "Implementation error (useful)"

        (Fix (PCon _ con rs):_, _) ->
            let special = specialized con (getTag <$> rs)
             in useful (special px) (head (special [qs]))

        (_:qs1, _) -> do
            cs <- headCons px
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) ->
                    let special = specialized con (getTag <$> rs)
                     in useful (special px) (head (special [qs]))) 
                else useful (defaultMatrix px) qs1
  where
    complete [] = 
        pure False
    complete names@(name:_) = do
        defined <- ask
        let constructors = defined `Env.union` builtIn
        pure (Env.findWithDefaultEmpty name constructors == Set.fromList names)

    builtIn = constructorEnv
        [ ("$True",     ["$True", "$False"])
        , ("$False",    ["$True", "$False"])
        , ("$()",       ["$()"])
        , ("$Int",      [])
        , ("$Integer",  [])
        , ("$Float",    [])
        , ("$Char",     [])
        , ("$String",   []) 
        ]

exhaustive :: (MonadReader ConstructorEnv m) => [[Pattern t]] -> m Bool
exhaustive []        = pure False
exhaustive px@(ps:_) = not <$> useful px (anyPat . getTag <$> ps)

--
--
--
--
--
--
--
--
--
--
--


--data MatrixF t a 
--    = Matrix [[Pattern t]] [Pattern t]
--    | Bozz [a]
--    deriving (Show, Eq, Functor, Foldable, Traversable)
--
--type Matrix t = Fix (MatrixF t)
--
--data BorkF m a 
--    = Result Bool
--    | Next (m a)
--    | Or [a]
--    deriving (Show, Eq, Functor, Foldable, Traversable)
--
--type Bork m = Fix (BorkF m)
--
--franslate :: (MonadReader ConstructorEnv m) => Matrix t -> Bork m
--franslate = futu $ project >>> \case
--    Matrix [] _ ->
--        Result True
--
--    Matrix px@(ps:_) qs 
--        | null ps -> Result False
--        | null qs -> error "Implementation error (franslate)"
--        | otherwise ->
--            Next $ case qs of
--                Fix (PCon _ con rs):_ -> 
--                    let special = specialized con (getTag <$> rs)
--                    in -- useful (special px) (head (special [qs]))
--                    pure (Pure (Fix (Matrix (special px) (head (special [qs])))))
--
--                _:qs1 -> do
--                    cs <- headCons px
--                    isComplete <- complete (fst <$> cs)
--                    if isComplete
--                        then do
--                            xs <- cs & traverse (\(con, rs) ->
--                                let special = specialized con (getTag <$> rs)
--                                 in pure (Fix (Matrix (special px) (head (special [qs])))))
--                            pure (Pure (Fix (Bozz xs)))
--                        else 
--                            pure undefined -- (Pure (Free undefined) -- Pure (Fix (Matrix (defaultMatrix px) qs1)))
--    Bozz (x:xs) -> do
--        Next (pure (Pure x))
--  where
--    complete [] = 
--        pure False
--    complete names@(name:_) = do
--        defined <- ask
--        let constructors = defined `Env.union` builtIn
--        pure (Env.findWithDefaultEmpty name constructors == Set.fromList names)
--
--    builtIn = constructorEnv
--        [ ("$True",     ["$True", "$False"])
--        , ("$False",    ["$True", "$False"])
--        , ("$()",       ["$()"])
--        , ("$Int",      [])
--        , ("$Integer",  [])
--        , ("$Float",    [])
--        , ("$Char",     [])
--        , ("$String",   []) ]
