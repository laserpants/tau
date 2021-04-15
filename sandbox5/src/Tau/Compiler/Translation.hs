{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Translation where

import Control.Monad.Supply
import Tau.Lang
import Tau.Tool
import Tau.Type

data ClauseA t p a = ClauseA t [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

data Prep t = RCon t Name [Name]
    deriving (Show, Eq)

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

class (Show t, Eq t) => TypeTag t where
    tvar  :: Name -> t
    tarr  :: t -> t -> t
    tapp  :: t -> t -> t

instance TypeTag () where
    tvar _   = ()
    tarr _ _ = ()
    tapp _ _ = ()

instance TypeTag Type where
    tvar  = tVar kTyp
    tarr  = tArr
    tapp  = tApp

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

expandClauseGuards
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam (Clause  t (ProgPattern t))
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam (ClauseA t (ProgPattern t))
expandClauseGuards = cata $ \case
    EPat t es cs -> patExpr t es (expandClause =<< cs)
    EFun t cs    -> funExpr t    (expandClause =<< cs)
  where
    expandClause (Clause t ps gs) = [ClauseA t ps es e | Guard es e <- gs]

translateTuples
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ()  t14 t15 bind lam clause 
translateTuples =
    undefined

translateLists 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ()  t15 bind lam clause 
translateLists =
    undefined

translateRecords 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ()  bind lam clause 
translateRecords =
    undefined

translateUnaryOps 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ()  t12 t13 t14 t15 bind lam clause 
translateUnaryOps =
    undefined

translateBinaryOps 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ()  t13 t14 t15 bind lam clause 
translateBinaryOps =
    undefined

translateFunExprs
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 ()  t11 t12 t13 t14 t15 bind lam clause 
translateFunExprs =
    undefined

translateLetExprs 
  :: (TypeTag t, MonadSupply Name m, Traversable clause) 
  => Expr t t t t t t t t t t t t t t t (Binding t (Pattern t t t t t t t t t)) [Pattern t t t t t t t t t] clause
  -> m (Expr t t t t t t t t t t t t t t t (Pattern t t t t t t t t t) [Pattern t t t t t t t t t] clause)
translateLetExprs = cata $ \case

    EVar    t var        -> pure $ varExpr t var
    ECon    t con es     -> conExpr t con <$> sequence es
    ELit    t prim       -> pure $ litExpr t prim
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e       -> lamExpr t ps <$> e
    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
    EPat    t es cs      -> patExpr t <$> sequence es <*> traverse sequence cs
    EFun    t cs         -> funExpr t <$> traverse sequence cs
    EOp1    t op a       -> op1Expr t op <$> a
    EOp2    t op a b     -> op2Expr t op <$> a <*> b
    ETuple  t es         -> tupleExpr t <$> sequence es
    EList   t es         -> listExpr t <$> sequence es
    ERecord t row        -> recordExpr t <$> sequence row

    ELet t (BLet _ pat) e1 e2 -> 
        letExpr t pat <$> e1 <*> e2

    ELet t (BFun _ f ps) e1 e2 -> do
        vars <- supplies (length ps)
        e <- e1
        let t1 = foldr tarr (exprTag e) (patternTag <$> ps)
        letExpr t (varPat t1 f) (lamExpr t1 ps e) <$> e2

translateLamExprs 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind Name pat 
translateLamExprs =
    undefined

translateTuplePatterns
  :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
  -> Pattern t1 t2 t3 t4 t5 t6 () t8 t9
translateTuplePatterns =
    undefined

translateListPatterns
  :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
  -> Pattern t1 t2 t3 t4 t5 t6 t7 () t9
translateListPatterns =
    undefined

translateRecordPatterns
  :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
  -> Pattern t1 t2 t3 t4 t5 t6 t7 t8 ()
translateRecordPatterns =
    undefined

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

compilePatterns (u:us) qs c =
    case clauseGroups qs of
        [Variable eqs] ->
            undefined

        [Constructor eqs] -> do
            undefined

        mixed -> 
            undefined

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

clauseGroups 
  :: [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a] 
  -> [Labeled [Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a]]
clauseGroups = cata alg . fmap labeledClause where

    alg Nil                                        = []
    alg (Cons (Constructor e) (Constructor es:ts)) = Constructor (e:es):ts
    alg (Cons (Variable e) (Variable es:ts))       = Variable (e:es):ts
    alg (Cons (Constructor e) ts)                  = Constructor [e]:ts
    alg (Cons (Variable e) ts)                     = Variable [e]:ts

labeledClause 
  :: Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a 
  -> Labeled (Clause t (Pattern t1 t2 t3 t4 () t6 t7 t8 t9) a)
labeledClause eq@(Clause _ (p:_) _) = flip cata p $ \case

    PCon{}    -> Constructor eq
    PTuple{}  -> Constructor eq
    PRecord{} -> Constructor eq
    PList{}   -> Constructor eq
    PVar{}    -> Variable eq
    PAny{}    -> Variable eq
    PLit{}    -> Variable eq
    PAs _ _ q -> q
