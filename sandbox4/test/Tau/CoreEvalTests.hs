{-# LANGUAGE OverloadedStrings #-}
module Tau.CoreEvalTests where

import Data.Maybe (fromJust, isNothing)
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Eval.Core
import Test.Hspec
import Utils
import qualified Tau.Util.Env as Env

testValueEnv :: ValueEnv Eval
testValueEnv = Env.fromList
    [ ("(,)"     , constructor "(,)" 2)  
    , ("first"   , fromJust (evalExpr first_ mempty))
    , ("second"  , fromJust (evalExpr second_ mempty))
    ]
  where
    first_  = cLam "p" (cPat (cVar "p") [(["(,)", "a", "b"], cVar "a")])
    second_ = cLam "p" (cPat (cVar "p") [(["(,)", "a", "b"], cVar "b")])

failEval :: Core -> SpecWith ()
failEval expr =
    describe ("The expression " <> prettyString expr) $
        it "✗ fails to evaluate" $
            isNothing (evalExpr expr testValueEnv)

succeedEval :: Core -> Value Eval -> SpecWith ()
succeedEval expr val =
    describe ("The expression " <> prettyString expr) $
        it ("✔ evaluates to the value " <> prettyString val) $
            evalExpr expr testValueEnv == Just val

succeedEvalToFunction :: Core -> SpecWith ()
succeedEvalToFunction expr =
    describe ("The expression " <> prettyString expr) $
        it "✔ evaluates to a function"
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
        (cLet "id" (cLam "x" (cVar "x")) (cLet "x" (cApp [cVar "(,)", cVar "id", cLit (LInt 4)]) (cApp [cVar "@Int.(+)", cApp [cApp [cVar "first", cVar "x"], cApp [cVar "second", cVar "x"]], cLit (LInt 1)])))       
        (Value (LInt 5))

