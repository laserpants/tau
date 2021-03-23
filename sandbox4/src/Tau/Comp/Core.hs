{-# LANGUAGE EmptyDataDeriving    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE StrictData           #-}
module Tau.Comp.Core where

import Control.Arrow
import Control.Monad.Error.Class (liftEither)
import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List (nub)
import Data.List.Extra (groupSortOn)
import Data.Maybe (fromJust, fromMaybe)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (both, thd3)
import Data.Void
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution hiding (null)
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

--class TypeTag t where
--class (Eq t, Show t) => TypeTag t where
class (Eq t) => TypeTag t where
    tvar  :: Name -> t
    tarr  :: t -> t -> t
    tapp  :: t -> t -> t
    tbool :: t

instance TypeTag () where
    tvar _   = ()
    tarr _ _ = ()
    tapp _ _ = ()
    tbool    = ()

instance TypeTag Type where
    tvar  = tVar kTyp
    tarr  = tArr
    tapp  = tApp
    tbool = tBool

---- TODO
--data GuardsExpanded 
--    deriving (Show, Eq)

data PatternsExpanded 
    deriving (Show, Eq)

data PatternsDesugared 
    deriving (Show, Eq)

data NoListSugar
    deriving (Show, Eq)

data NoFunPats
    deriving (Show, Eq)

compileExpr :: (TypeTag t, MonadSupply Name m) => Ast t (Op1 t) (Op2 t) -> m Core
compileExpr = desugarOperators >>> compileExpr3 

compileExpr3 :: (TypeTag t, MonadSupply Name m) => Ast t Void Void -> m Core
compileExpr3 =
    expandGuards
    >>> expandFunPatterns
    >=> pure . desugarLists
    >=> unrollLets
    >=> simplify
    >=> toCore
    >=> optimizeCore

--compileExpr3 :: (TypeTag t, MonadSupply Name m) => Ast t Void Void -> m Core
--compileExpr3 e = do
--    let xxx = expandGuards e
--    traceShowM e
--    traceShowM "&&&&&&&&&&&"
--    traceShowM xxx
--    traceShowM "&&&&&&&&&&&"
--
--    yyy <- expandFunPatterns xxx
--
--    let zzz = desugarLists yyy
--
--    traceShowM zzz
--    traceShowM "&&&&&&&&&&&"
--
--    aa1 <- unrollLets zzz
--    bb1 <- simplify aa1
--
--    traceShowM bb1
--    traceShowM "&&&&&&&&&&&"
--
--    cc1 <- toCore bb1
--    --traceShowM (prettyCoreTree (optimizeCore cc1))
--
--    traceShowM cc1
--    traceShowM "&&&&&&&&&&&"
--
--    xx123 <- optimizeCore cc1
--
--    traceShowM xx123
--    traceShowM "&&&*********"
--
--    pure xx123

--    >>> expandFunPatterns
--    >=> pure . desugarLists
--    >=> unrollLets
--    >=> simplify
--    >=> toCore
--    >=> optimizeCore



--compileExpr
--  :: (Pretty (Expr t (Prep t) Name Name Void Void), TypeTag t, MonadSupply Name m)
--  => Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] Void Void
--  -> m Core
--compileExpr e = do
--    a <- expandFunPatterns e
--    let aa = desugarLists a
--    --traceShowM (pretty a)
--    --traceShowM "1-------------------------------"
--    b <- unrollLets aa
--    traceShowM b
--    traceShowM "2-*-----------------------------"
--    c <- simplify b
--    traceShowM c
--    traceShowM "3-------------------------------"
--    d <- toCore c
--    traceShowM d
--    traceShowM "4-------------------------------"
--    pure d

expandGuards :: Ast t p q -> Ast t p q
expandGuards = cata $ \case
    EPat t es qs -> patExpr t es (expandClause =<< qs)
    e            -> embed e
  where
    expandClause (Clause ps guards) = 
        [Clause ps [g] | g <- guards]

expandFunPatterns
  :: (MonadSupply Name m)
  => Ast t p q
  -> m (Expr t (Pattern t () ()) (Binding (Pattern t () ())) [Pattern t () ()] Void Void c NoFunPats)
expandFunPatterns = cata $ \case

    EPat t [] exs@(Clause ps [Guard _ e]:_) -> do
        (_, exprs, pats) <- patternInfo varPat ps
        body <- e
        let e1 = patExpr (exprTag body) exprs
        lamExpr t pats . e1 <$> traverse sequence exs

    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    ELet t b e1 e2   -> letExpr t b <$> e1 <*> e2
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    ELam t pat e1    -> lamExpr t pat <$> e1
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    -- TODO: change naming of variables.. EPat t es qs
    EPat t eqs exs   -> patExpr t <$> sequence eqs <*> traverse sequence exs
    EDot t e1 e2     -> dotExpr t <$> e1 <*> e2
    ERec t fields    -> recExpr t <$> sequence fields
    ETup t exs       -> tupExpr t <$> sequence exs
    ELst t a         -> lstExpr t <$> sequence a

unrollLets
--  :: (TypeTag t, MonadSupply Name m)
--  => Expr t p (Binding (Pattern t f g)) [Pattern t f g] Void Void NoListSugar NoFunPats
--  -> m (Expr t p (Pattern t f g) [Pattern t f g] Void Void NoListSugar NoFunPats)
  :: (TypeTag t, MonadSupply Name m)
  => Expr t p (Binding (Pattern t () ())) [Pattern t () ()] Void Void NoListSugar NoFunPats
  -> m (Expr t p (Pattern t () ()) [Pattern t () ()] Void Void NoListSugar NoFunPats)
unrollLets = cata $ \case

    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    ELam t pat e1    -> lamExpr t pat <$> e1
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    EPat t eqs exs   -> patExpr t <$> sequence eqs <*> traverse sequence exs
    EDot t e1 e2     -> dotExpr t <$> e1 <*> e2
    ERec t fields    -> recExpr t <$> sequence fields
    ETup t exs       -> tupExpr t <$> sequence exs

    ELet t (BLet pat) e1 e2 ->
        letExpr t pat <$> e1 <*> e2

    ELet t (BFun f ps) e1 e2 -> do
        vars <- supplies (length ps)
        expr <- e1
        let t1 = foldr tarr (exprTag expr) (patternTag <$> ps)
        letExpr t (varPat t1 f) (lamExpr t1 ps expr) <$> e2

simplify
  :: (TypeTag t, MonadSupply Name m)
  => Expr t (Pattern t () ()) (Pattern t () ()) [Pattern t () ()] Void Void NoListSugar NoFunPats
  -> m (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)
simplify = cata $ \case
    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    EDot t e1 e2     -> dotExpr t <$> e1 <*> e2
    ERec t fields    -> recExpr t <$> sequence fields
    ETup t exs       -> tupExpr t <$> sequence exs

    -- TODO: Check for disallowed patterns
    --   let _ = e
    --   let 5 = e

    ELet t (Fix (PVar _ var)) e1 e2 ->
        letExpr t var <$> e1 <*> e2

    ELet _ pat e1 e2 -> do
        expr <- e1
        body <- e2
        exs <- expandPatterns [Clause [pat] [Guard [] body]]
        compilePatterns [expr] exs

    ELam _ ps e1 -> do
        (vars, exprs, _) <- patternInfo varPat ps
        body <- e1
        expr <- expandPatterns [Clause ps [Guard [] body]] >>= compilePatterns exprs
        let toLam v t e = lamExpr (tarr t (exprTag e)) v e
        pure (foldr (uncurry toLam) expr vars)

    EPat _ eqs exs -> do
        exs1 <- traverse sequence exs
        join (compilePatterns <$> sequence eqs <*> expandPatterns exs1)

expandPatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Clause (Pattern t () g) (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)]
  -> m [Clause (Pattern t PatternsExpanded g) (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)]
expandPatterns = (toExpanded <$$>) . expandLitPatterns . expandOrPatterns 
  where
    toExpanded (Clause ps [e]) = 
        Clause (patternsExpanded <$> ps) [e]

    patternsExpanded = cata $ \case
        PVar t a       -> varPat t a
        PCon t a b     -> conPat t a b
        PRec t s       -> recPat t s
        PTup t a       -> tupPat t a
        PLst t a       -> lstPat t a
        PAny t         -> anyPat t
        PAs  t a b     -> asPat t a b
        _              -> error "Implementation error"

expandLitPatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Clause (Pattern t f g) (Expr t p q r n o c d)]
  -> m [Clause (Pattern t f g) (Expr t p q r n o c d)]
expandLitPatterns = traverse expandClause
  where
    expandClause (Clause ps [Guard exs e]) = do
        (qs, exs1) <- runWriterT (traverse expand1 ps)
        pure (Clause qs [Guard (exs <> exs1) e])

--    expandClause (Clause ps exs e) = do
--        (qs, exs1) <- runWriterT (traverse expand1 ps)
--        pure (Clause qs (exs <> exs1) e)

    expand1 = cata $ \case
        PLit t lit -> do
            var <- supply
            tell [appExpr tbool
                     [ varExpr (tarr t (tarr t tbool)) ("@" <> literalName lit <> ".(==)")
                     , varExpr t var
                     , litExpr t lit ]]
            pure (varPat t var)

        p ->
            embed <$> sequence p

expandOrPatterns :: [Clause (Pattern t f g) a] -> [Clause (Pattern t f g) a]
expandOrPatterns = concatMap $ \(Clause ps [e]) ->
    [Clause qs [e] | qs <- traverse fork ps]
  where
    fork :: Pattern t f g -> [Pattern t f g]
    fork = cata $ \case 
        PCon t con ps  -> conPat t con <$> sequence ps
        PTup t ps      -> tupPat t <$> sequence ps
        PRec t fields  -> recPat t <$> sequence fields
        PLst t ps      -> lstPat t <$> ps
        PAs  t name a  -> asPat t name <$> a
        POr  _ a b     -> a <> b
        p              -> embed <$> sequence p 

--    fork :: Pattern t f g -> [Pattern t f g]
--    fork = project >>> \case
--        PCon t con ps  -> conPat t con <$> traverse fork ps
--        PTup t ps      -> tupPat t <$> traverse fork ps
--        PRec t fields  -> recPat t <$> traverse fork fields
--        PLst t ps      -> lstPat t <$> traverse fork ps
--        PAs  t name a  -> asPat t name <$> fork a
--        POr  _ a b     -> fork a <> fork b
--        p              -> [embed p]

compilePatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats]
  -> [Clause (Pattern t PatternsExpanded g) (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)]
  -> m (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)
compilePatterns us qs = matchAlgo us qs (varExpr (tvar "FAIL") "FAIL")

andExpr :: (TypeTag t) => Expr t p q r n o c d -> Expr t p q r n o c d -> Expr t p q r n o c d
andExpr a b = appExpr tbool [varExpr (tarr tbool (tarr tbool tbool)) "@(&&)", a, b]

-- | based on the pattern matching compilers described in [1] and [2] ...
--
-- References:
--
--   - [1] Augustsson L. (1985) Compiling pattern matching.
--   - [2] Peyton Jones, Simon & Lester, David. (2000). Implementing functional languages: a tutorial. 
--
-- In this stage ...
--
--   - ...
--   - List patterns [1, 2, 3] (so called list literals) are translated to 1 :: 2 :: 3 :: []
--
--matchAlgo
--  :: (TypeTag t, MonadSupply Name m)
--  => [Expr t (Prep t) Name Name Void Void]
--  -> [Clause (Pattern t PatternsExpanded PatternsDesugared) (Expr t (Prep t) Name Name Void Void)]
--  -> Expr t (Prep t) Name Name Void Void
--  -> m (Expr t (Prep t) Name Name Void Void)
matchAlgo
  :: (TypeTag t, MonadSupply Name m)
  => [Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats]
  -> [Clause (Pattern t PatternsExpanded g) (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)]
  -> Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats
  -> m (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)
matchAlgo [] []                           c = pure c
matchAlgo [] (Clause [] [Guard [] e]:_)   _ = pure e
matchAlgo [] (Clause [] [Guard exs e]:qs) c =
    ifExpr (exprTag c) (foldr1 andExpr exs) e <$> matchAlgo [] qs c
matchAlgo (u:us) qs c =
    case clauseGroups qs of
        [Variable eqs] ->
            matchAlgo us (runSubst <$> eqs) c
          where
            runSubst (Clause (Fix (PVar t name):ps) [Guard exs e]) =
                substitute name u <$> Clause ps [Guard exs e]

            runSubst (Clause (Fix (PAs _ as (Fix (PVar t name))):ps) [Guard exs e]) = 
                substitute name u . substitute as (varExpr t name) <$> Clause ps [Guard exs e]

            runSubst (Clause (Fix (PAs _ as (Fix (PAny t))):ps) [Guard exs e]) = 
                substitute as u <$> Clause ps [Guard exs e]

            -- The remaining case is for wildcard and literal patterns
            runSubst (Clause (Fix _:ps) [Guard exs e]) =
                Clause ps [Guard exs e]

--            runSubst (Clause (Fix (PVar t name):ps) exs e) =
--                substitute name u <$> Clause ps exs e
--
--            runSubst (Clause (Fix (PAs _ as (Fix (PVar t name))):ps) exs e) = 
--                substitute name u . substitute as (varExpr t name) <$> Clause ps exs e
--
--            runSubst (Clause (Fix (PAs _ as (Fix (PAny t))):ps) exs e) = 
--                substitute as u <$> Clause ps exs e
--
--            -- The remaining case is for wildcard and literal patterns
--            runSubst (Clause (Fix _:ps) exs e) =
--                Clause ps exs e

        [Constructor eqs@(Clause _ [Guard _ e]:_)] -> do
            qs' <- traverse (toSimpleMatch c) (consGroups u eqs)
            --pure $ case qs' <> [Clause [RCon (exprTag u) "$_" []] [] c | not (isError c)] of
            pure $ case qs' <> [Clause [RCon (exprTag u) "$_" []] [Guard [] c] | not (isError c)] of
                []   -> c
                qs'' -> patExpr (exprTag e) [u] qs''

          where
            toSimpleMatch c ConsGroup{..} = do
                (_, vars, pats) <- patternInfo (const id) consPatterns
                expr <- matchAlgo (vars <> us) consClauses c
                pure (Clause [RCon consType consName pats] [Guard [] expr])

            isError :: Expr t p q r n o c d -> Bool
            isError = cata $ \case
                EVar _ var | "FAIL" == var -> True
                _                          -> False


--        [Constructor eqs@(Clause _ _ e:_)] -> do
--            qs' <- traverse (toSimpleMatch c) (consGroups u eqs)
--            pure $ case qs' <> [Clause [RCon (exprTag u) "$_" []] [] c | not (isError c)] of
--                []   -> c
--                qs'' -> patExpr (exprTag e) [u] qs''
--
--          where
--            toSimpleMatch c ConsGroup{..} = do
--                (_, vars, pats) <- patternInfo (const id) consPatterns
--                expr <- matchAlgo (vars <> us) consClauses c
--                pure (Clause [RCon consType consName pats] [] expr)
--
--            isError :: Expr t p q r n o c d -> Bool
--            isError = cata $ \case
--                EVar _ var | "FAIL" == var -> True
--                _                          -> False
--
        mixed -> do
            foldrM (matchAlgo (u:us)) c (clauses <$> mixed)



--matchAlgo [] (Clause [] exs e:qs) c =
--    ifExpr (exprTag c) (foldr1 andExpr exs) e <$> matchAlgo [] qs c

--matchAlgo [] (Clause [] []  e:_)  _ = pure e
--matchAlgo [] (Clause [] exs e:qs) c =
--    ifExpr (exprTag c) (foldr1 andExpr exs) e <$> matchAlgo [] qs c
--matchAlgo (u:us) qs c =
--    case clauseGroups qs of
--        [Variable eqs] ->
--            matchAlgo us (runSubst <$> eqs) c
--          where
--            runSubst (Clause (Fix (PVar t name):ps) exs e) =
--                substitute name u <$> Clause ps exs e
--
--            runSubst (Clause (Fix (PAs _ as (Fix (PVar t name))):ps) exs e) = 
--                substitute name u . substitute as (varExpr t name) <$> Clause ps exs e
--
--            runSubst (Clause (Fix (PAs _ as (Fix (PAny t))):ps) exs e) = 
--                substitute as u <$> Clause ps exs e
--
--            -- The remaining case is for wildcard and literal patterns
--            runSubst (Clause (Fix _:ps) exs e) =
--                Clause ps exs e
--
--        [Constructor eqs@(Clause _ _ e:_)] -> do
--            qs' <- traverse (toSimpleMatch c) (consGroups u eqs)
--            pure $ case qs' <> [Clause [RCon (exprTag u) "$_" []] [] c | not (isError c)] of
--                []   -> c
--                qs'' -> patExpr (exprTag e) [u] qs''
--
--          where
--            toSimpleMatch c ConsGroup{..} = do
--                (_, vars, pats) <- patternInfo (const id) consPatterns
--                expr <- matchAlgo (vars <> us) consClauses c
--                pure (Clause [RCon consType consName pats] [] expr)
--
--            isError :: Expr t p q r n o c d -> Bool
--            isError = cata $ \case
--                EVar _ var | "FAIL" == var -> True
--                _                          -> False
--
--        mixed -> do
--            foldrM (matchAlgo (u:us)) c (clauses <$> mixed)

data ConsGroup t = ConsGroup 
    { consName     :: Name
    , consType     :: t
    , consPatterns :: [Pattern t PatternsExpanded PatternsDesugared]
    , consClauses  :: [Clause (Pattern t PatternsExpanded PatternsDesugared) (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)]
    } deriving (Show, Eq)

consGroups 
  :: Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats 
  -> [Clause (Pattern t PatternsExpanded g) (Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats)] 
  -> [ConsGroup t]
consGroups u cs = concatMap grp (groupSortOn fst (info <$> cs))
  where
    grp all@((con, (t, ps, _)):_) = 
        [ConsGroup { consName     = con
                   , consType     = t
                   , consPatterns = patternsDesugared <$> ps
                   , consClauses  = clauseDesugared <$> (thd3 . snd <$> all) 
                   }]

    info (Clause (p:qs) [Guard exs e]) =
        case project (desugarPattern p) of
            PCon t con ps -> (con, (t, ps, Clause (ps <> qs) [Guard exs e]))
            PAs _ as q    -> info (Clause (q:qs) [Guard exs (substitute as u e)])

--    info (Clause (p:qs) exs e) =
--        case project (desugarPattern p) of
--            PCon t con ps ->
--                (con, (t, ps, Clause (ps <> qs) exs e))
--
--            PAs _ as q ->
--                info (Clause (q:qs) exs (substitute as u e))

    patternsDesugared = cata $ \case
        PVar t a       -> varPat t a
        PCon t a b     -> conPat t a b
        PAny t         -> anyPat t
        PAs  t a b     -> asPat t a b
        _              -> error "Implementation error"

    clauseDesugared (Clause ps [Guard exs e]) = 
        Clause (patternsDesugared <$> ps) [Guard exs e]

--    clauseDesugared (Clause ps ex e) = 
--        Clause (patternsDesugared <$> ps) ex e

desugarPattern :: Pattern t f g -> Pattern t f g
desugarPattern = cata $ \case
    PRec t (FieldSet fields) ->
        conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields)
    PTup t elems ->
        conPat t (tupleCon (length elems)) elems
    PLst t elems ->
        foldr (listConsPat t) (conPat t "[]" []) elems
    p ->
        embed p

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

labeledClause :: Clause (Pattern t f g) a -> Labeled (Clause (Pattern t f g) a)
labeledClause eq@(Clause (p:_) _) = flip cata p $ \case

      PCon{}    -> Constructor eq
      PTup{}    -> Constructor eq
      PRec{}    -> Constructor eq
      PLst{}    -> Constructor eq
      PVar{}    -> Variable eq
      PAny{}    -> Variable eq
      PLit{}    -> Variable eq
      PAs _ _ q -> q
      POr{}     -> error "Implementation error"

--      f = project >>> \case
--          POr{}     -> error "Implementation error"
--          PAs _ _ q -> f q
--          PCon{}    -> Constructor eq
--          PTup{}    -> Constructor eq
--          PRec{}    -> Constructor eq
--          PLst{}    -> Constructor eq
--          PVar{}    -> Variable eq
--          PAny{}    -> Variable eq
--          PLit{}    -> Variable eq

clauseGroups :: [Clause (Pattern t f g) a] -> [Labeled [Clause (Pattern t f g) a]]
clauseGroups = cata alg . fmap labeledClause where
    alg Nil                                        = []
    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
    alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
    alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
    alg (Cons (Variable e) ts)                     = Variable [e]:ts

patternInfo
  :: (MonadSupply Name m)
  => (t -> Name -> a)
  -> [Pattern t f g]
  -> m ([(Name, t)], [Expr t p q r n o c d], [a])
patternInfo con pats = do
    vars <- supplies (length pats)
    let ts = patternTag <$> pats
        make c = uncurry c <$> zip ts vars
    pure (zip vars ts, make varExpr, make con)

substitute
  :: Name
  -> Expr t (Prep t) Name Name n o c d
  -> Expr t (Prep t) Name Name n o c d
  -> Expr t (Prep t) Name Name n o c d
substitute name subst = para $ \case
    ELet t pat (_, e1) e2 -> letExpr t pat e1 e2'
      where
        e2' | name == pat = fst e2
            | otherwise   = snd e2

    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EPat t exs eqs ->
        patExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq eq@(Clause ps _)
            | name `elem` (pats =<< ps) = fst <$> eq
            | otherwise                 = snd <$> eq
        pats (RCon _ _ ps) = ps

    expr -> snd <$> expr & \case
        EVar t var
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e

sequenceExs :: (Monad m) => [m Core] -> m Core
sequenceExs = (fun <$>) . sequence where 
    fun = \case 
        [e] -> e
        xs  -> cApp xs

toCore :: (MonadSupply Name m) => Expr t (Prep t) Name Name Void Void NoListSugar NoFunPats -> m Core
toCore = cata $ \case

    EVar _ var       -> pure (cVar var)
    ELit _ lit       -> pure (cLit lit)
    EIf  _ e1 e2 e3  -> cIf <$> e1 <*> e2 <*> e3
    EApp _ exs       -> sequenceExs exs
    ECon _ con exs   -> sequenceExs (pure (cVar con):exs)
    ELet _ var e1 e2 -> cLet var <$> e1 <*> e2
    EFix _ var e1 e2 -> cLet var <$> e1 <*> e2
    ELam _ var e1    -> cLam var <$> e1
    EDot _ e1 e2     -> sequenceExs [e2, e1]

    ERec _ (FieldSet fields) -> do
        exprs <- traverse fieldValue fields
        pure (cApp (cVar (recordCon (fieldName <$> fields)):exprs))

    ETup _ exs -> do
        exprs <- sequence exs
        pure (cApp (cVar (tupleCon (length exs)):exprs))

    EPat _ eqs exs -> 
        sequence eqs >>= \case
            [expr] -> cPat expr <$> traverse desugarClause exs
            _      -> error "Implementation error"
  where
    desugarClause (Clause [RCon _ con ps] [Guard [] e]) = 
        (,) (con:ps) <$> e
    desugarClause _ =
        error "Implementation error"

--    desugarClause (Clause [RCon _ con ps] [] e) = 
--        (,) (con:ps) <$> e
--    desugarClause _ =
--        error "Implementation error"

optimizeCore :: (MonadSupply Name m) => Core -> m Core
optimizeCore = cata $ \case

    CIf e1 e2 e3 -> do
        a <- project <$> e2
        b <- project <$> e3
        if a == b || CVar "FAIL" == b
            then e2
            else cIf <$> e1 <*> e2 <*> e3

    e -> embed <$> sequence e

desugarOperators :: Expr t p q r (Op1 t) (Op2 t) () () -> Expr t p q r Void Void () ()
desugarOperators = cata $ \case

    EOp1 t op a -> 
        appExpr t [prefix1 op, a]

    EOp2 t op a b -> 
        appExpr t [prefix2 op, a, b]

    EVar t var       -> varExpr t var
    ECon t con exs   -> conExpr t con exs
    ELit t lit       -> litExpr t lit
    EApp t exs       -> appExpr t exs
    ELet t e1 e2 e3  -> letExpr t e1 e2 e3
    EFix t var e1 e2 -> fixExpr t var e1 e2
    ELam t pat e1    -> lamExpr t pat e1
    EIf  t e1 e2 e3  -> ifExpr  t e1 e2 e3
    EPat t eqs exs   -> patExpr t eqs exs
    EDot t name e1   -> dotExpr t name e1
    ERec t fields    -> recExpr t fields
    ETup t exs       -> tupExpr t exs
    ELst t exs       -> lstExpr t exs

  where
    prefix1 (ONeg t) = varExpr t "negate"
    prefix1 (ONot t) = varExpr t "not"
    prefix2 op = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")

desugarLists :: Expr t p q r n o c d -> Expr t p q r n o NoListSugar d
desugarLists = cata $ \case
    ELst t exs       -> foldr (listConsExpr t) (conExpr t "[]" []) exs
    EVar t var       -> varExpr t var
    ECon t con exs   -> conExpr t con exs
    ELit t lit       -> litExpr t lit
    EApp t exs       -> appExpr t exs
    ELet t e1 e2 e3  -> letExpr t e1 e2 e3
    EFix t var e1 e2 -> fixExpr t var e1 e2
    ELam t pat e1    -> lamExpr t pat e1
    EIf  t e1 e2 e3  -> ifExpr  t e1 e2 e3
    EPat t eqs exs   -> patExpr t eqs exs
    EOp1 t op a      -> op1Expr t op a
    EOp2 t op a b    -> op2Expr t op a b
    EDot t name e1   -> dotExpr t name e1
    ERec t fields    -> recExpr t fields
    ETup t exs       -> tupExpr t exs

-- ============================================================================
-- Type classes
-- ============================================================================

compileClasses 
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv, TypeEnv) m)
  => Ast (NodeInfoT Type) Void Void
  -> StateT [(Name, Type)] m (Ast (NodeInfoT Type) Void Void) 
compileClasses expr = 
    insertDictArgs <$> run expr <*> (nub <$> pluck)
  where
    run = cata $ \case

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            xs <- nub <$> pluck
            letExpr t pat (insertDictArgs e1 xs) <$> expr2

        EVar t var -> 
            foldrM applyDicts (varExpr (stripNodePredicates t) var) (nodePredicates t)

        e -> 
            embed <$> sequence e

insertDictArgs :: Ast NodeInfo p q -> [(Name, Type)] -> Ast NodeInfo p q
insertDictArgs expr = foldr fun expr
  where
    fun (a, b) = lamExpr (NodeInfo (tArr b (typeOf expr)) []) [varPat (NodeInfo b []) a] 

--collect :: (MonadState [(Name, Type)] m) => m [(Name, Type)]
--collect = nub <$> pluck

applyDicts
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv, TypeEnv) m)
  => Predicate
  -> Ast (NodeInfoT Type) Void Void
  -> StateT [(Name, Type)] m (Ast (NodeInfoT Type) Void Void)
applyDicts (InClass name ty) expr 

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        let t = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
            dict = varExpr (NodeInfo t []) tv
        modify ((tv, t) :)
        let expr' = setExprTag (NodeInfo (t `tArr` typeOf expr) []) expr
        pure (appExpr (exprTag expr) [expr', dict])

    | otherwise = do
        env <- asks fst
        case lookupClassInstance name ty env of
            Left e -> throwError e
            Right (_, (_, _, methods)) -> do

                -- TODO: super-classes???

                xxx <- traverse blob methods
                let yy = fieldSet xxx
                    ttt = tRecord (typeOf <$$> methods)
                    dict = recExpr (NodeInfo ttt []) yy

                let def = appExpr (exprTag expr) 
                            [ setExprTag (NodeInfo (typeOf dict `tArr` typeOf expr) []) expr
                            , dict ]

                pure $ case (project expr, project dict) of
                    (EVar _ var, ERec _ fields) -> 
                        maybe def snd (lookupField var fields)
                    _ -> 
                        def



--            Right (_ , Instance{..}) -> do
--
--                -- TODO: super-classes???
--
--                dict <- compileClasses (desugarOperators instanceDict)
--
--                let def = appExpr (exprTag expr) 
--                            [ setExprTag (NodeInfo (typeOf dict `tArr` typeOf expr) []) expr
--                            , dict ]
--
--                pure $ case (project expr, project dict) of
--                    (EVar _ var, ERec _ fields) -> 
--                        maybe def snd (lookupField var fields)
--                    _ -> 
--                        def

--blob (a, b) = Field (exprTag foo) a <$> compileClasses (desugarOperators b)

----blob :: (Name, ProgExpr) -> m (Name, (Ast (NodeInfoT Type) Void Void f))
blob (a, b) = do
    foo <- compileClasses (desugarOperators b)
    --foo <- compileClasses b
    pure (Field (exprTag foo) a foo)
                        
setNodeType :: Type -> NodeInfo -> NodeInfo
setNodeType ty info = info{ nodeType = ty }

setNodePredicates :: [Predicate] -> NodeInfoT a -> NodeInfoT a
setNodePredicates ps info = info{ nodePredicates = ps }

stripNodePredicates :: NodeInfoT a -> NodeInfoT a
stripNodePredicates = setNodePredicates []

-- ============================================================================
-- Pattern anomalies check
-- ============================================================================

type ConstructorEnv = Env (Set Name)

constructorEnv :: [(Name, [Name])] -> ConstructorEnv
constructorEnv = Env.fromList . (Set.fromList <$$>)

headCons :: [[Pattern t f g]] -> [(Name, [Pattern t f g])]
headCons = (>>= fun) 
  where
    fun :: [Pattern t f g] -> [(Name, [Pattern t f g])]
    fun [] = error "Implementation error (headCons)"
    fun (p:ps) = 
        case project p of
            PLit _ lit -> 
                [(prim lit, [])]

            PCon _ name rs -> 
                [(name, rs)]

            PRec t (FieldSet fields) ->
                fun (conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields):ps)

            PTup t elems ->
                fun (conPat t (tupleCon (length elems)) elems:ps)

            PLst t elems ->
                fun (foldr (listConsPat t) (conPat t "[]" []) elems:ps)

            PAs _ _ q -> 
                fun (q:ps)

            POr _ a b -> 
                fun (a:ps) <> fun (b:ps)

            _ -> 
                []

    prim (TBool True)  = "#True"
    prim (TBool False) = "#False"
    prim TUnit         = "#()"
    prim TInt{}        = "#Int"
    prim TInteger{}    = "#Integer"
    prim TFloat{}      = "#Float"
    prim TDouble{}     = "#Double"
    prim TChar{}       = "#Char"
    prim TString{}     = "#String"

defaultMatrix :: [[Pattern t f g]] -> [[Pattern t f g]]
defaultMatrix = (fun =<<)
  where 
    fun :: [Pattern t f g] -> [[Pattern t f g]]
    fun (p:ps) =
        case project p of
            PCon{}    -> []
            PRec{}    -> []
            PTup{}    -> []
            PLst{}    -> []
            PLit{}    -> []
            PAs _ _ q -> fun (q:ps)
            POr _ q r -> fun (q:ps) <> fun (r:ps)
            _         -> [ps]

--defaultMatrix :: [[Pattern t f g]] -> [[Pattern t f g]]
--defaultMatrix = undefined -- concatMap fun2
--
--boss :: [Pattern t f g] -> [[Pattern t f g]]
--boss = ana $ \case
--    (Fix PCon{}:_)       -> Nil
--    (Fix PRec{}:_)       -> Nil
--    (Fix PTup{}:_)       -> Nil
--    (Fix PLst{}:_)       -> Nil
--    (Fix PLit{}:_)       -> Nil
--    (Fix (PAs _ _ q):ps) -> Cons ps []
--    (Fix _:ps)           -> Cons ps []
--    _                    -> Nil
--
--fun :: Pattern t f g -> [Pattern t f g]
--fun = cata $ \case
--    PCon{}    -> []
--    PRec{}    -> []
--    PTup{}    -> []
--    PLst{}    -> []
--    PLit{}    -> []
--    PAs _ _ q -> [q]
--    POr _ q r -> [q, r]
----    _         -> []
--
--defaultMatrix33 :: (Show t, Show f, Show g) => [[Pattern t f g]] -> [[Pattern t f g]]
--defaultMatrix33 = concatMap boss

--fun2 :: (Show t, Show f, Show g) => [Pattern t f g] -> [[Pattern t f g]]
--fun2 = para $ \case
--
--    Cons (Fix PCon{}) _       -> []
--    Cons (Fix PRec{}) _       -> []
--    Cons (Fix PTup{}) _       -> []
--    Cons (Fix PLst{}) _       -> []
--    Cons (Fix PLit{}) _       -> []
--    Cons (Fix (PAs _ _ q)) ps -> traceShow q $ traceShow ps $ [fst ps] -- traceShow q $ traceShow ps $ []
----    Cons (Fix (POr _ q r)) ps -> ([q]:ps) <> ([r]:ps)
--    Cons _                 ps -> [fst ps]
--    Nil                       -> []

--fun2 (p:ps) = flip cata p $ \case
--
--    PCon{}    -> []
--    PRec{}    -> []
--    PTup{}    -> []
--    PLst{}    -> []
--    PLit{}    -> []
----    PAs _ _ q -> let xx = q <> ps in undefined
----    POr _ q r -> q <> [ps] <> r <> [ps] -- fun2 (q:ps) <> fun2 (r:ps)
--    _         -> [ps]


specialized :: Name -> [t] -> [[Pattern t f g]] -> [[Pattern t f g]]
specialized name ts = concatMap rec 
  where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ con rs
                | con == name -> [rs <> ps]
                | otherwise   -> []

            PRec t (FieldSet fields) -> do
                -- TODO: DRY
                let q = conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields)
                rec (q:ps)

            PTup t elems -> do
                -- TODO: DRY
                let q = conPat t (tupleCon (length elems)) elems
                rec (q:ps)

            PLst t elems -> do
                -- TODO: DRY
                let q = foldr (listConsPat t) (conPat t "[]" []) elems
                rec (q:ps)

            PAs _ _ q ->
                rec (q:ps)

            POr _ p1 p2 ->
                rec (p1:ps) <> rec (p2:ps)

            _ ->
                [(anyPat <$> ts) <> ps]

-- TODO: rename
data AType t f g
    = ACon Name [Pattern t f g] 
    | AOr (Pattern t f g) (Pattern t f g) 
    | AAny

getA :: Pattern t f g -> AType t f g
getA = project >>> \case
    PCon _ con rs -> 
        ACon con rs

    PRec t (FieldSet fields) -> 
        -- TODO: DRY
        getA (conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields))

    PTup t elems ->
        -- TODO: DRY
        getA (conPat t (tupleCon (length elems)) elems)

    PLst t elems ->
        -- TODO: DRY
        getA (foldr (listConsPat t) (conPat t "[]" []) elems)

    PAs _ _ a -> 
        getA a

    POr _ a b -> 
        AOr a b

    _ -> 
        AAny

-- |
--
-- References:
--
--   - http://moscova.inria.fr/~maranget/papers/warn/ 
--
useful :: (MonadReader ConstructorEnv m) => [[Pattern t f g]] -> [Pattern t f g] -> m Bool
useful [] _   = pure True   -- Zero rows (0x0 matrix)
useful (p1:_) qs 
    | null p1 = pure False  -- One or more rows but no columns
    | null qs = error "Implementation error (useful)"
useful pss (q:qs) =
    case getA q of
        ACon con rs  ->
            let special = specialized con (patternTag <$> rs)
             in useful (special pss) (head (special [q:qs]))
        AAny -> do
            let cs = headCons pss
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) ->
                    let special = specialized con (patternTag <$> rs)
                     in useful (special pss) (head (special [q:qs]))) 
                else 
                    useful (defaultMatrix pss) qs
        AOr a b -> 
            useful pss (a:qs) ||^ useful pss (b:qs)
  where
    complete [] = pure False
    complete names@(name:_) = do
        defined <- ask
        pure (lookupCon (defined `Env.union` builtIn) name == Set.fromList names)
    lookupCon constructors con 
        | isTupleCon con || isRecordCon con = Set.singleton con
        | otherwise = Env.findWithDefaultEmpty con constructors

    builtIn = constructorEnv
        [ ("#True",     ["#True", "#False"])
        , ("#False",    ["#True", "#False"])
        , ("#()",       ["#()"])
        , ("#Int",      [])
        , ("#Integer",  [])
        , ("#Float",    [])
        , ("#Char",     [])
        , ("#String",   []) 
        , ("[]",        ["[]", "(::)"]) 
        , ("(::)",      ["[]", "(::)"]) 
        , ("Zero",      ["Zero", "Succ"]) 
        , ("Succ",      ["Zero", "Succ"]) 
        ]

isTupleCon :: Name -> Bool
isTupleCon con = Just True == (allCommas <$> stripped con)
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

isRecordCon :: Name -> Bool
isRecordCon con = ("{", "}") == fstLst con
  where
    fstLst ""  = ("", "")
    fstLst con = both Text.singleton (Text.head con, Text.last con)

exhaustive :: (MonadReader ConstructorEnv m) => [[Pattern t f g]] -> m Bool
exhaustive []         = pure False
exhaustive pss@(ps:_) = not <$> useful pss (anyPat . patternTag <$> ps)

-- TODO: DRY
type PatternClauseX = Clause (Pattern () () ()) (Ast () (Op1 ()) (Op2 ()))

clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [PatternClauseX] -> m Bool
clausesAreExhaustive = exhaustive . concatMap toMatrix
  where
    toMatrix (Clause ps guards)
        | null guards           = [ps]
        | any isCatchAll guards = [ps]
    toMatrix _ =
        []

    isCatchAll (Guard [ ] _)             = True
    isCatchAll (Guard [b] _) | b == true = True where true = litExpr () (TBool True)
    isCatchAll _                         = False

--clausesAreExhaustiveY = undefined
--
----clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [Clause (Pattern t f g) (m Bool)] -> m Bool
--clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [Clause (Pattern t f g) (m Bool)] -> m Bool
--clausesAreExhaustive = undefined -- exhaustive . concatMap toMatrix 
----  where
----    toMatrix (Clause ps [Guard gs _]) = do
----        undefined
----
------    toMatrix (Clause ps [Guard gs _]) 
------        | null gs               = [ps]
------        | any (== undefined) gs = [ps]
----
----    toMatrix _ = []
--
--    toMatrix (Clause ps [Guard [] _]) = [ps]

--    toMatrix (Clause ps [] _) = [ps]
--    toMatrix _                = []

--cata $ \case

-- | Determine if all patterns in the expression are exhaustive.
--
checkExhaustive :: (MonadReader ConstructorEnv m) => Ast () (Op1 ()) (Op2 ()) -> m Bool
checkExhaustive = para $ \case

    EPat _ eqs exs -> 
        andM (snd <$> eqs) &&^ clausesAreExhaustive (fst <$$> exs)

    expr -> snd <$> expr & \case
        ECon _ _ exprs           -> andM exprs
        EApp _ exprs             -> andM exprs
        ELet _ (BLet p) e1 e2    -> exhaustive [[p]] &&^ e1 &&^ e2
        ELet _ (BFun f ps) e1 e2 -> exhaustive [ps] &&^ e1 &&^ e2
        EFix _ _ e1 e2           -> e1 &&^ e2
        ELam _ ps e1             -> exhaustive [ps] &&^ e1
        EIf  _ cond tr fl        -> cond &&^ tr &&^ fl
        EOp1 _ _ a               -> a
        EOp2 _ _ a b             -> a &&^ b
        EDot _ a b               -> a &&^ b
        ERec _ (FieldSet fields) -> andM (fieldValue <$> fields)
        ETup _ elems             -> andM elems
        ELst _ elems             -> andM elems
        _                        -> pure True

astApply :: Substitution -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo)
astApply sub = mapTags (apply sub :: NodeInfo -> NodeInfo)

extractType :: Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) -> Ast Type (Op1 Type) (Op2 Type)
extractType = (mapTags :: (NodeInfo -> Type) -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) -> Ast Type (Op1 Type) (Op2 Type)) nodeType

extractType2 :: Ast NodeInfo Void Void -> Ast Type Void Void
extractType2 = (mapTags :: (NodeInfo -> Type) -> Ast NodeInfo Void Void -> Ast Type Void Void) nodeType

--toUnitType :: Expr t (Prep t) Name Name Void Void -> Expr () (Prep ()) Name Name Void Void
--toUnitType = mapTags (const ())
