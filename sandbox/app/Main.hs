module Main where

import Tau.Expr
import Tau.Expr.Patterns
import Tau.Type
import Tau.Type.Solver
import Tau.Type.Substitution
import Tau.Type.Inference


-- let x = 3 in f x

testExpr1 :: PatternExpr ()
testExpr1 =
    eLet 
        (rVar () "x") 
        (tagLit () (LInt 3)) 
        (tagApp () [eVar "f", tagVar () "x"])

test1 = r where Right r = runInfer (infer testExpr1)

-- let (Just x) = (Just 3) in x

testRep2 :: Rep ()
testRep2 = rCon () "Just" [rVar () "x"]

testExpr2 :: PatternExpr ()
testExpr2 =
    eLet 
        testRep2
        (tagApp () [tagVar () "Just", tagLit () (LInt 3)]) 
        (tagVar () "x")

runTestRep2 :: (Rep Type, [TypeAssumption])
runTestRep2 = r where Right r = runInfer (inferRep testRep2)

test2 :: (RepExpr Type, [TypeAssumption], [Constraint])
test2 = r where Right r = runInfer (infer testExpr2)

test2Sub = sub
  where
    (tr, as, cs) = test2
    Right (sub, tycls) = runInfer (solve cs)

test22 :: Infer (RepExpr Type)
test22 = do
    (tr, as, cs) <- infer testExpr2
    (sub, tycls) <- solve cs
    pure (apply sub tr)

runTest22 = runInfer test22

--

-- match x with 
--   | Just 3 :: [] => e1
--   | Just x :: [] => e2
--
testExpr3 =
    tagMatch ()
      [tagVar () "x"]
      [ Equation [pCon () "Cons" [pCon () "Just" [pLit () (LInt 3)], pCon () "Nil" []]] [] (tagVar () "e1") 
      , Equation [pCon () "Cons" [pCon () "Just" [pVar () "x"], pCon () "Nil" []]] [] (tagVar () "e2") 
      ]

test3 = do
    (tr, as, cs) <- infer testExpr3
    pure tr

runTest3 = runInfer test3


main :: IO ()
main = pure ()
