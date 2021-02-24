{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StrictData           #-}
module Tau.Comp.Core where

import Control.Arrow
import Control.Monad
import Control.Monad.Supply 
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util

class TypeTag t where
    tvar :: Name -> t
    tarr :: t -> t -> t
    tapp :: t -> t -> t

instance TypeTag () where
    tvar _   = ()
    tarr _ _ = ()
    tapp _ _ = ()

instance TypeTag Type where
    tvar = tVar kTyp
    tarr = tArr
    tapp = tApp

pipeline
  :: (TypeTag t, MonadSupply Name m) 
  => Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] 
  -> m (Expr t Rep Name Name)
pipeline =
    expandFunPats 
    >=> unrollLets
    >=> simplify

expandFunPats 
  :: (MonadSupply Name m) 
  => Expr t (Pattern t) q [Pattern t] 
  -> m (Expr t (Pattern t) q [Pattern t])
expandFunPats = cata $ \case

    EPat t [] exs@(Clause ps _ e:_) -> do
        --vars <- supplies (length ps)
        --expr <- e
        --let make c = uncurry c <$> zip ts vars
        --    ts = patternTag <$> ps
        --    e1 = patExpr (exprTag expr) (make varExpr)
        --lamExpr t (make varPat) . e1 <$> traverse sequence exs
        
        (body, _, exprs, pats) <- patternInfo ps e
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

--simplify1
--  :: (MonadSupply Name m) 
--  => Expr t (Pattern t) q [Pattern t] 
--  -> m (Expr t (Pattern t) q [Pattern t])
--simplify1 = cata $ \case
    --EVar t var       -> pure (varExpr t var)
    --ECon t con exs   -> conExpr t con <$> sequence exs
    --ELit t lit       -> pure (litExpr t lit)
    --EApp t exs       -> appExpr t <$> sequence exs
    --EFix t var e1 e2 -> fixExpr t var <$> e1 <*> e2
    --EIf  t e1 e2 e3  -> ifExpr  t <$> e1 <*> e2 <*> e3
    --EOp1 t op a      -> op1Expr t op <$> a
    --EOp2 t op a b    -> op2Expr t op <$> a <*> b
    --EDot t name e1   -> dotExpr t name <$> e1
    --ERec t fields    -> recExpr t <$> sequence fields
    --ETup t exs       -> tupExpr t <$> sequence exs

--    ELet t b e1 e2 -> 
--        letExpr t b <$> e1 <*> e2

--    ELam t pat e1 -> 
--        lamExpr t pat <$> e1

--    EPat t eqs exs -> 
--        patExpr t <$> sequence eqs 
--                  <*> traverse sequence exs
--    e -> 
--        embed <$> sequence e

simplify
  :: (TypeTag t, MonadSupply Name m) 
  => Expr t (Pattern t) (Pattern t) [Pattern t] 
  -> m (Expr t Rep Name Name)
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
        compilePatterns [expr] (expandOrPats [Clause [pat] [] body])

    ELam t ps e1 -> do
        (body, vars, exprs, pats) <- patternInfo ps e1
        expr <- compilePatterns exprs (expandOrPats [Clause pats [] body])
        let toLam v t e = lamExpr (tarr t (exprTag e)) v e
        pure (foldr (uncurry toLam) expr vars)

    EPat t eqs exs -> 
        join (compilePatterns <$> sequence eqs 
                              <*> traverse sequence (expandOrPats exs))

expandOrPats :: [Clause (Pattern t) a] -> [Clause (Pattern t) a]
expandOrPats = concatMap f 
  where
    f :: Clause (Pattern t) a -> [Clause (Pattern t) a]
    f (Clause ps exs e) = [Clause qs exs e | qs <- traverse fork ps]

    fork :: Pattern t -> [Pattern t]
    fork = project >>> \case 
        PCon t con ps   -> conPat t con <$> traverse fork ps
        PTup t ps       -> tupPat t <$> traverse fork ps
        PRec t fields   -> recPat t <$> traverse fork fields
        PAs  t name a   -> asPat t name <$> fork a
        POr  _ a b      -> fork a <> fork b 
        p               -> [Fix p]

compilePatterns 
  :: (MonadSupply Name m) 
  => [a]
  -> [Clause (Pattern t) a]
  -> m (Expr t Rep Name Name)
compilePatterns =
    undefined

matchAlgo 
  :: (MonadSupply Name m) 
  => [a]
  -> [Clause (Pattern t) (Expr t Rep Name Name)]
  -> Expr t Rep Name Name
  -> m (Expr t Rep Name Name)
matchAlgo [] [] c                 = pure c
matchAlgo [] (Clause [] [] e:_) _ = pure e

matchAlgo (u:us) eqs c =
    undefined

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

labeledClause :: Clause (Pattern t) a -> Labeled (Clause (Pattern t) a)
labeledClause eq@(Clause (p:ps) _ _) = f p
  where
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
  => [Pattern t] 
  -> m (Expr t p q r) 
  -> m (Expr t p q r, [(Name, t)], [Expr t p q r], [Pattern t])
patternInfo pats expr = do
    vars <- supplies (length pats)
    body <- expr
    let ts = patternTag <$> pats
        make c = uncurry c <$> zip ts vars
    pure (body, zip vars ts, make varExpr, make varPat)

--expandFunPats 
--  :: (MonadSupply Name m) 
--  => Expr t (Pattern t) q [Pattern t] 
--  -> m (Expr t (Pattern t) q [Pattern t])
--expandFunPats = cata $ \case
--    EPat t [] exs@(Clause ps _ e:_) -> do
--        vars <- supplies (length ps)
--        expr <- e
--        let make c = uncurry c <$> zip ts vars
--            ts = patternTag <$> ps
--            e1 = patExpr (exprTag expr) (make varExpr)
--        lamExpr t (make varPat) . e1 <$> traverse sequence exs

toCore 
  :: (MonadSupply Name m) 
  => Expr t p q r
  -> m Core
toCore =
    undefined
