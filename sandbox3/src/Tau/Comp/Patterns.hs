{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Comp.Patterns where
-- Tau.Comp.Sugar
-- Tau.Comp.Core

import Control.Applicative ((<|>))
import Control.Arrow
import Control.Monad
import Control.Monad.Except
import Control.Monad.Extra (maybeM, anyM)
import Control.Monad.Free 
import Control.Monad.Reader
import Control.Monad.Supply 
import Control.Monad.Trans.Free (FreeT(..))
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List (sort)
import Data.List.Extra (groupSortOn, groupBy, sortOn)
import Data.Maybe (fromJust, fromMaybe, maybeToList)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (fst3, snd3, thd3)
import Debug.Trace
import Tau.Util.Env
import Tau.Lang.Pretty
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Control.Monad.Free as Monad
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

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
    = Match [Expr t (Prep t) Name Name] [Clause (Pattern t) (Expr t (Prep t) Name Name)] a
    | Fail
    deriving (Show, Eq, Functor, Foldable, Traversable)

type MatchExpr t = Fix (MatchExprF t)

data TranslatedF m t a
    = Wrap (m a)
    | SimpleMatch a [(Prep t, a)]
    | If a a a
    | Expr (Expr t (Prep t) Name Name)
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Translated m t = Fix (TranslatedF m t)

deriveShow1 ''MatchExprF
deriveEq1   ''MatchExprF

deriveShow1 ''TranslatedF
deriveEq1   ''TranslatedF

class Boolean t where
    boolean :: t
    arrow   :: t -> t -> t
    fromArr :: t -> (t, t)

instance Boolean () where
    boolean   = ()
    arrow _ _ = ()
    fromArr _ = ((), ())

instance Boolean Type where
    boolean   = tBool
    arrow     = tArr 
    fromArr f = case project f of (TArr dom cod) -> (dom, cod)

simplified 
  :: (Boolean t, Show t) 
  => Expr t (Pattern t) (Let (Pattern t)) [Pattern t]
  -> Either String (Expr t (Prep t) Name Name)
simplified = runSimplify . simplify . unrollAsPats . unrollLambdas
--simplified = runSimplify . simplify . unrollOrPats . unrollAsPats . unrollLambdas

unrollOrPats 
  :: (Boolean t) 
  => Expr t (Pattern t) (Let (Pattern t)) (Pattern t)
  -> Expr t (Pattern t) (Let (Pattern t)) (Pattern t)
unrollOrPats = cata $ \case
    ELam t ps a                -> undefined
    ELet t (Let p) e1 e2       -> undefined
    ELet t (LetFun f ps) e1 e2 -> undefined
    EPat t exs eqs             -> patExpr t exs (clause =<< eqs)
    e                          -> embed e
  where
    clause (Clause ps exs e) = 
        undefined


unrollAsPats 
  :: (Boolean t) 
  => Expr t (Pattern t) (Let (Pattern t)) (Pattern t)
  -> Expr t (Pattern t) (Let (Pattern t)) (Pattern t)
unrollAsPats = cata $ \case
    ELam t ps a                 -> let ([qs], rs) = run [ps] in lamExpr t qs (foldr fun a rs)
    ELet t (Let p) e1 e2        -> let ([qs], rs) = run [p] in letExpr t (Let qs) e1 (foldr fun e2 rs)
    ELet t (LetFun f ps) e1 e2  -> let (qs, rs) = run ps in letExpr t (LetFun f qs) e1 (foldr fun e2 rs)
    EPat t exs eqs              -> patExpr t exs (clause <$> eqs)
    e                           -> embed e
  where
    fun (name, p) e = 
        patExpr (exprTag e) [varExpr (patternTag p) name] [Clause [p] [] e]

    clause (Clause ps exs e) = 
        let (qs, rs) = run ps in Clause qs exs (foldr fun e rs)

    run ps = second concat (unzip (split <$> ps))

    split :: Pattern t -> (Pattern t, [(Name, Pattern t)])
    split (Fix (PAs t name p)) = (varPat t name, [(name, p)])
    split p                    = (p, [])

unrollLambdas
  :: (Boolean t) 
  => Expr t (Pattern t) (Let (Pattern t)) [Pattern t]
  -> Expr t (Pattern t) (Let (Pattern t)) (Pattern t)
unrollLambdas = cata $ \case
    ELam _ ps a       -> foldr unrolled a ps
    EVar t var        -> varExpr t var
    ECon t con exs    -> conExpr t con exs
    ELit t lit        -> litExpr t lit
    EApp t exs        -> appExpr t exs
    EFix t name e1 e2 -> fixExpr t name e1 e2
    ELet t pat e1 e2  -> letExpr t pat e1 e2
    EIf  t cond e1 e2 -> ifExpr  t cond e1 e2
    EPat t [] eqs ->
        let (dom, cod) = fromArr t
         in unrolled (varPat dom "$0") (patExpr cod [varExpr dom "$0"] eqs)
    EPat t exs eqs    -> patExpr t exs eqs
    EOp  t op         -> opExpr  t op
    ERec t fields     -> recExpr t fields
  where
    unrolled pat ex = lamExpr (arrow (patternTag pat) (exprTag ex)) pat ex

simplify 
  :: (Boolean t, Show t) 
  => Expr t (Pattern t) (Let (Pattern t)) (Pattern t)
  -> Simplify (Expr t (Prep t) Name Name)
simplify = cata $ \case
    EVar t var     -> pure (varExpr t var)
    ECon t con exs -> conExpr t con <$> sequence exs
    ELit t lit     -> pure (litExpr t lit)
    EApp t exs     -> appExpr t <$> sequence exs

    --
    --  Let-expressions can only bind to variables patterns (formal parameters)
    --
    ELet t (Let (Fix (PVar _ var))) e1 e2 -> 
        letExpr t var <$> e1 <*> e2

    ELet t (LetFun f ps) e1 e2 -> 
        letExpr t f <$> foldr fffn e1 ps <*> e2

    --
    --  The same restriction applies to lambdas
    --
    ELam t (Fix (PVar _ var)) e1 -> 
        lamExpr t var <$> e1 

    --
    --  Expressions like \5 => ..., let 5 = ..., or let _ = ... are not allowed
    --
    ELam _ (Fix PLit{}) _         -> throwError "Pattern not allowed"
    ELet _ (Let (Fix PLit{})) _ _ -> throwError "Pattern not allowed"
    ELet _ (Let (Fix PAny{})) _ _ -> throwError "Pattern not allowed"

    --
    --  Expressions like let C x = y in f x
    --  get translated to: match y with | C x => f x
    --
    ELet _ (Let rep) e1 e2 -> do
        expr <- e1
        body <- e2
        compile [expr] [Clause [rep] [] body]

    EFix t name e1 e2 -> 
        fixExpr t name <$> e1 <*> e2

    --
    --  Lambda expressions like \(C x) => f x
    --  get translated to \$z => match $z with | C x => f x in $z
    --  where $z is a fresh variable
    --
    ELam t rep e1 -> 
        simplifyLam t rep e1

    EIf t cond e1 e2 ->
        ifExpr t <$> cond <*> e1 <*> e2

    EPat t exs eqs ->
        join (compile <$> sequence exs <*> traverse sequence eqs)

    EOp t op ->
        simplifyOp t op

    ERec t fields ->
        recExpr t <$> traverse sequence fields

simplifyLam 
  :: (Boolean t, Show t)
  => t
  -> Pattern t
  -> Simplify (Expr t (Prep t) Name Name)
  -> Simplify (Expr t (Prep t) Name Name)
simplifyLam t rep e1 = do
    fresh <- supply
    body <- e1
    lamExpr t fresh <$> compile [varExpr t fresh] [Clause [rep] [] body]

fffn
  :: (Boolean t, Show t) 
  => Pattern t
  -> Simplify (Expr t (Prep t) Name Name)
  -> Simplify (Expr t (Prep t) Name Name)
fffn pat ex = do
    e1 <- ex
    simplifyLam (arrow (patternTag pat) (exprTag e1)) pat ex

simplifyOp :: t -> Op (Simplify (Expr t p q r)) -> Simplify (Expr t p q r)
simplifyOp t (OEq  a b) = eqOp  t <$> a <*> b
simplifyOp t (OAnd a b) = andOp t <$> a <*> b
simplifyOp t (OOr  a b) = orOp  t <$> a <*> b
simplifyOp t (OAdd a b) = addOp t <$> a <*> b
simplifyOp t (OSub a b) = subOp t <$> a <*> b
simplifyOp t (OMul a b) = mulOp t <$> a <*> b
simplifyOp t (ODot name a) = dotOp t name <$> a

flatten 
  :: (Boolean t, Show t, Show p, Show q) 
  => Clause (Pattern t) (Expr t p q r) 
  -> Clause (Pattern t) (Expr t p q r)
flatten (Clause ps exs e) = Clause qs (exs <> exs1) e
  where
    (qs, exs1) = fromJust (evalSupply fun (nameSupply "="))
    fun = second concat . unzip <$> traverse (runWriterT . cata alg) ps

    alg = \case
        PAny t -> 
            pure (varPat t "$_")

        PLit t lit -> do
            var <- supply
            tell [eqOp boolean (varExpr t var) (litExpr t lit)]
            pure (varPat t var)

        PRec t fields -> do
            let info = fieldsInfo fields
            ps <- traverse thd3 info
            pure (conPat t ("{" <> Text.intercalate "," (snd3 <$> info) <> "}") ps)

        PAs t name p -> 
            error "Implementation error" 

        pat ->
            embed <$> sequence pat

compile 
  :: (Boolean t, Show t) 
  => [Expr t (Prep t) Name Name]
  -> [Clause (Pattern t) (Expr t (Prep t) Name Name)]
  -> Simplify (Expr t (Prep t) Name Name)
compile es qs = 
    Match es (flatten <$> qs) (embed Fail)
      & embed
      & translate  
      & collapse 
  where
    collapse 
      :: Translated Simplify t 
      -> Simplify (Expr t (Prep t) Name Name)
    collapse = cata $ \case
        Wrap a -> join a
        Expr a -> pure a
        If cond tr fl -> 
            ifExpr <$> (exprTag <$> tr) 
                   <*> cond 
                   <*> tr 
                   <*> fl
        SimpleMatch ex css -> do
            expr <- ex
            (eqs, ts) <- unzip <$> traverse fn css
            pure (patExpr (head ts) [expr] eqs)
          where
            fn (rep, ex1) = do
                expr <- ex1
                pure ( Clause [rep] [] expr
                     , exprTag expr )

translate :: (Show t) => MatchExpr t -> Translated Simplify t
translate = futu $ project >>> \case
    Fail ->
        Wrap (throwError "Fail")

    Match [] [] c ->
        Wrap (pure (Pure c))

    Match [] (Clause [] [] e:_) _ ->
        Expr e

    Match [] (Clause [] exs e:qs) c ->
        If (Free (Expr (foldr1 (\a -> andOp (exprTag a) a) exs))) 
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
                        uncurry (varExpr . patternTag) <$> zip ps vs

            mixed -> do
                pure (Pure (embed (foldr fn (project c) (getEqs <$> mixed))))
              where
                getEqs (ConTag a) = a
                getEqs (VarTag a) = a

                fn eqs a = Match (u:us) eqs (embed a)

--- 
--- 

substitute 
  :: Name 
  -> Expr t (Prep t) Name Name
  -> Expr t (Prep t) Name Name
  -> Expr t (Prep t) Name Name
substitute name subst = para $ \case
    ELet t pat (_, e1) e2 -> letExpr t pat e1 e2'
      where 
        e2' | name == pat = fst e2
            | otherwise   = snd e2

    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EPat t exs eqs -> patExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq eq@(Clause ps _ _) 
            | name `elem` free ps = fst <$> eq
            | otherwise           = snd <$> eq

    expr -> snd <$> expr & \case
        EVar t var 
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e

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
    fun ps = pure $ case project (head ps) of
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
            let special = specialized con (patternTag <$> rs)
             in useful (special px) (head (special [qs]))

        (_:qs1, _) -> do
            cs <- headCons px
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) ->
                    let special = specialized con (patternTag <$> rs)
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
exhaustive px@(ps:_) = not <$> useful px (anyPat . patternTag <$> ps)

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
