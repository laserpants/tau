{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE StrictData           #-}
module Tau.Comp.Core where

import Control.Arrow
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List.Extra (groupSortOn)
import Data.Tuple.Extra (thd3)
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util

class TypeTag t where
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

pipeline
  :: (TypeTag t, MonadSupply Name m)
  => Expr t (Pattern t) (Binding (Pattern t)) [Pattern t]
  -> m Core
pipeline = expandFunPats
    >=> unrollLets
    >=> simplify
    >=> toCore

--pipeline
--  :: (TypeTag t, MonadSupply Name m)
--  => Expr t (Pattern t) (Binding (Pattern t)) [Pattern t]
--  -> m Core
--pipeline e = do
--    a <- expandFunPats e
--    b <- unrollLets a
--    c <- simplify b
--    toCore c

expandFunPats
  :: (MonadSupply Name m)
  => Expr t (Pattern t) q [Pattern t]
  -> m (Expr t (Pattern t) q [Pattern t])
expandFunPats = cata $ \case

    EPat t [] exs@(Clause ps _ e:_) -> do
        (_, exprs, pats) <- patternInfo varPat ps
        body <- e
        let e1 = patExpr (exprTag body) exprs
        lamExpr t pats . e1 <$> traverse sequence exs

    e ->
        embed <$> sequence e

unrollLets
  :: (TypeTag t, MonadSupply Name m)
  => Expr t p (Binding (Pattern t)) [Pattern t]
  -> m (Expr t p (Pattern t) [Pattern t])
unrollLets = cata $ \case

    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    ELam t pat e1    -> lamExpr t pat <$> e1
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    EPat t eqs exs   -> patExpr t <$> sequence eqs <*> traverse sequence exs
    EOp1 t op a      -> op1Expr t op <$> a
    EOp2 t op a b    -> op2Expr t op <$> a <*> b
    EDot t name e1   -> dotExpr t name <$> e1
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
  => Expr t (Pattern t) (Pattern t) [Pattern t]
  -> m (Expr t (Prep t) Name Name)
simplify = cata $ \case
    EVar t var       -> pure (varExpr t var)
    ECon t con exs   -> conExpr t con <$> sequence exs
    ELit t lit       -> pure (litExpr t lit)
    EApp t exs       -> appExpr t <$> sequence exs
    EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    EOp1 t op a      -> op1Expr t op <$> a
    EOp2 t op a b    -> op2Expr t op <$> a <*> b
    EDot t name e1   -> dotExpr t name <$> e1
    ERec t fields    -> recExpr t <$> sequence fields
    ETup t exs       -> tupExpr t <$> sequence exs

    -- Check for disallowed patterns

    ELet t pat e1 e2 -> do
        expr <- e1
        body <- e2
        exs <- desugarPatterns [Clause [pat] [] body]
        compilePatterns [expr] exs

    ELam t ps e1 -> do
        (vars, exprs, _) <- patternInfo varPat ps
        body <- e1
        expr <- desugarPatterns [Clause ps [] body] >>= compilePatterns exprs
        let toLam v t e = lamExpr (tarr t (exprTag e)) v e
        pure (foldr (uncurry toLam) expr vars)

    EPat t eqs exs -> do
        exs1 <- traverse sequence exs
        join (compilePatterns <$> sequence eqs <*> desugarPatterns exs1)

desugarPatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Clause (Pattern t) (Expr t p q r)]
  -> m [Clause (Pattern t) (Expr t p q r)]
desugarPatterns = expandLitPats . expandOrPats

expandLitPats
  :: (TypeTag t, MonadSupply Name m)
  => [Clause (Pattern t) (Expr t p q r)]
  -> m [Clause (Pattern t) (Expr t p q r)]
expandLitPats = traverse expandClause
  where
    expandClause (Clause ps exs e) = do
        (qs, exs1) <- runWriterT (traverse expand1 ps)
        pure (Clause qs (exs <> exs1) e)

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

expandOrPats :: [Clause (Pattern t) a] -> [Clause (Pattern t) a]
expandOrPats = concatMap $ \(Clause ps exs e) ->
    [Clause qs exs e | qs <- traverse fork ps]
  where
    fork :: Pattern t -> [Pattern t]
    fork = project >>> \case
        PCon t con ps  -> conPat t con <$> traverse fork ps
        PTup t ps      -> tupPat t <$> traverse fork ps
        PRec t fields  -> recPat t <$> traverse fork fields
        PAs  t name a  -> asPat t name <$> fork a
        POr  _ a b     -> fork a <> fork b -- need to be the same set ????
        p              -> [embed p]

compilePatterns
  :: (TypeTag t, MonadSupply Name m)
  => [Expr t (Prep t) Name Name]
  -> [Clause (Pattern t) (Expr t (Prep t) Name Name)]
  -> m (Expr t (Prep t) Name Name)
compilePatterns us qs = matchAlgo us qs (varExpr (tvar "FAIL") "FAIL")

matchAlgo
  :: (TypeTag t, MonadSupply Name m)
  => [Expr t (Prep t) Name Name]
  -> [Clause (Pattern t) (Expr t (Prep t) Name Name)]
  -> Expr t (Prep t) Name Name
  -> m (Expr t (Prep t) Name Name)
matchAlgo [] []                   c = pure c
matchAlgo [] (Clause [] []  e:_)  _ = pure e
matchAlgo [] (Clause [] exs e:qs) c =
    ifExpr (exprTag c) (foldr1 (op2Expr tbool OAnd) exs) e <$> matchAlgo [] qs c
matchAlgo (u:us) qs c =
    case clauseGroups qs of
        [Variable eqs] -> do
            matchAlgo us (runSubst <$> eqs) c
          where
            runSubst c@(Clause (Fix (PVar t name):ps) exs e) =
                substitute name u <$> Clause ps exs e
            runSubst clause =
                clause

        [Constructor eqs@(Clause _ _ e:_)] -> do
            qs' <- traverse (toSimpleMatch c) (consGroups eqs)
            pure (patExpr (exprTag e) [u] qs')

          where
            toSimpleMatch c ConsGroup{..} = do
                (_, vars, pats) <- patternInfo (const id) consPatterns
                expr <- matchAlgo (vars <> us) consClauses c
                pure (Clause [RCon consType consName pats] [] expr)

        mixed -> do
            foldrM (matchAlgo (u:us)) c (clauses <$> mixed)

data ConsGroup t = ConsGroup
    { consName     :: Name
    , consType     :: t
    , consPatterns :: [Pattern t]
    , consClauses  :: [Clause (Pattern t) (Expr t (Prep t) Name Name)]
    } deriving (Show, Eq)

consGroups :: [Clause (Pattern t) (Expr t (Prep t) Name Name)] -> [ConsGroup t]
consGroups cs = concatMap grp (groupSortOn fst (info <$> cs))
  where
    grp all@((con, (t, ps, _)):_) =
        [ConsGroup con t ps (thd3 . snd <$> all)]

    info (Clause (p:qs) exs e) =
        case project (desugarPattern p) of
            PCon t con ps ->
                (con, (t, ps, Clause (ps <> qs) exs e))

desugarPattern :: Pattern t -> Pattern t
desugarPattern = cata $ \case
    PRec t (FieldSet fields) ->
        conPat t (recordCon (fieldName <$> fields)) (fieldValue <$> fields)
    PTup t elems ->
        conPat t (tupleCon (length elems)) elems
    p ->
        embed p

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

labeledClause :: Clause (Pattern t) a -> Labeled (Clause (Pattern t) a)
labeledClause eq@(Clause (p:_) _ _) = f p where
    f = project >>> \case
        POr{}     -> error "Implementation error"
        PAs _ _ q -> f q
        PCon{}    -> Constructor eq
        PTup{}    -> Constructor eq
        PRec{}    -> Constructor eq
        PVar{}    -> Variable eq
        PAny{}    -> Variable eq
        PLit{}    -> Variable eq

clauseGroups :: [Clause (Pattern t) a] -> [Labeled [Clause (Pattern t) a]]
clauseGroups = cata alg . fmap labeledClause where
    alg Nil = []
    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
    alg (Cons (Variable e) (Variable es:ts)) = Variable (e:es):ts
    alg (Cons (Constructor e) ts) = Constructor [e]:ts
    alg (Cons (Variable e) ts) = Variable [e]:ts

patternInfo
  :: (MonadSupply Name m)
  => (t -> Name -> a)
  -> [Pattern t]
  -> m ([(Name, t)], [Expr t p q r], [a])
patternInfo con pats = do
    vars <- supplies (length pats)
    let ts = patternTag <$> pats
        make c = uncurry c <$> zip ts vars
    pure (zip vars ts, make varExpr, make con)

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

    EPat t exs eqs ->
        patExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq eq@(Clause ps _ _)
            | name `elem` (pats =<< ps) = fst <$> eq
            | otherwise                 = snd <$> eq
        pats (RCon _ _ ps) = ps

    expr -> snd <$> expr & \case
        EVar t var
            | name == var -> subst
            | otherwise   -> varExpr t var

        e -> embed e

toCore
  :: (MonadSupply Name m)
  => Expr t (Prep t) Name Name
  -> m Core
toCore = cata $ \case
    EVar _ var       -> pure (cVar var)
    ELit _ lit       -> pure (cLit lit)
    EIf  _ e1 e2 e3  -> cIf <$> e1 <*> e2 <*> e3
    EApp _ exs       -> cApp <$> sequence exs
    ECon _ con exs   -> cApp <$> sequence (pure (cVar con):exs)
    ELet _ var e1 e2 -> cLet var <$> e1 <*> e2
--  EFix _ var e1 e2 -> cLet var <$> e1 <*> e2
    ELam _ var e1    -> cLam var <$> e1
    EOp1 _ op a      -> cApp <$> sequence [pure (prefix1 op), a]
    EOp2 _ op a b    -> cApp <$> sequence [pure (prefix2 op), a, b]
    EDot _ name e1   -> cApp <$> sequence [pure (cVar name), e1]

    ERec _ (FieldSet fields) -> do
        exprs <- traverse fieldValue fields
        pure (cApp (cVar (recordCon (fieldName <$> fields)):exprs))

    ETup _ exs -> do
        exprs <- sequence exs
        pure (cApp (cVar (tupleCon (length exs)):exprs))

    EPat _ eqs exs   -> do
        cs <- sequence eqs
        case cs of
            [expr] -> cPat expr <$> traverse desugarClause exs
            _      -> error "Implementation error"
  where
    prefix1 ONeg = cVar "negate"
    prefix1 ONot = cVar "not"
    prefix2 op = cVar ("(" <> opSymbol op <> ")")

    desugarClause (Clause [RCon _ con ps] exs e) =
        Clause (con:ps) <$> sequence exs <*> e
    desugarClause _ =
        error "Implementation error"
