{-# LANGUAGE OverloadedStrings #-}
module Tau.CoreEvalTests where

import Data.Maybe (isNothing)
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.TestEnvs
import Test.Hspec
import Utils

failEval :: Core -> SpecWith ()
failEval expr =
    describe ("The expression\n" <> prettyString expr) $
        it "✗ fails to evaluate\n" $
            isNothing (evalExpr expr testValueEnv)

succeedEval :: Core -> Value Eval -> SpecWith ()
succeedEval expr val =
    describe ("The expression\n" <> prettyString expr) $
        it ("✔ evaluates to the value " <> prettyString val <> "\n") $
            evalExpr expr testValueEnv == Just val

succeedEvalToFunction :: Core -> SpecWith ()
succeedEvalToFunction expr =
    describe ("The expression\n" <> prettyString expr) $
        it "✔ evaluates to a function\n"
            (Just True == (isClosure <$> evalExpr expr testValueEnv))
  where
    isClosure Closure{} = True
    isClosure _         = False

testCoreEval :: SpecWith ()
testCoreEval = do

    succeedEval
        (cApp [cLam "a" (cLam "b" (cVar "a")), cLit (LInt 5), cLit LUnit])
        (Value (LInt 5))

    failEval
        (cVar "hello")

    succeedEvalToFunction
        (cLam "a" (cLam "b" (cVar "a")))

    succeedEval
        (cLet "plus" (cLam "a" (cLam "b" (cApp [cVar "@Int.(+)", cVar "a", cVar "b"]))) (cLet "plus5" (cApp [cVar "plus", cLit (LInt 5)]) (cLet "id" (cLam "x" (cVar "x")) (cApp [cApp [cVar "id", cVar "plus5"], cApp [cVar "id", cLit (LInt 3)]]))))
        (Value (LInt 8))

    succeedEval
        (cApp [cLam "x" (cApp [cVar "@Int.(+)", cVar "x", cLit (LInt 1)]), cLit (LInt 1)])
        (Value (LInt 2))

    succeedEval
        (cLet "id" (cLam "x" (cVar "x")) (cLet "x" (cApp [cVar "(,)", cVar "id", cLit (LInt 4)]) (cApp [cVar "@Int.(+)", cApp [cApp [cVar "first", cVar "x"], cApp [cVar "second", cVar "x"]], cLit (LInt 1)])))       
        (Value (LInt 5))

    succeedEval
        (cIf (cLit (LBool True)) (cLit (LInt 1)) (cLit (LInt 2)))
        (Value (LInt 1))

    succeedEval
        (cIf (cLit (LBool False)) (cLit (LInt 1)) (cLit (LInt 2)))
        (Value (LInt 2))

    succeedEval
        (cApp [cLam "x" (cPat (cVar "x") [(["[]"], cLit (LInt 0)), (["(::)", "y", "ys"], cVar "y")]), cApp [cVar "(::)", cLit (LInt 5), cApp [cVar "[]"]]])
        (Value (LInt 5))
