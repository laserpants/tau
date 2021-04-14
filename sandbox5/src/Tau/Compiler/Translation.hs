{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Translation where

import Tau.Lang
import Tau.Tool

data Prep t = RCon t Name [Name]
    deriving (Show, Eq)

translateTuples
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ()  t14 t15 bind lam pat 
translateTuples =
    undefined

translateLists 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ()  t15 bind lam pat 
translateLists =
    undefined

translateRecords 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ()  bind lam pat 
translateRecords =
    undefined

translateUnaryOps 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ()  t12 t13 t14 t15 bind lam pat 
translateUnaryOps =
    undefined

translateBinaryOps 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ()  t13 t14 t15 bind lam pat 
translateBinaryOps =
    undefined

translateFunExprs
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 ()  t11 t12 t13 t14 t15 bind lam pat 
translateFunExprs =
    undefined

translateLetExprs 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
  -> Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) lam pat 
translateLetExprs =
    undefined

translateLamExprs 
  :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam pat 
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

data Labeled a = Constructor a | Variable a
    deriving (Show, Eq, Ord)

clauses :: Labeled a -> a
clauses (Constructor eqs) = eqs
clauses (Variable    eqs) = eqs

clauseGroups =
    undefined

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
