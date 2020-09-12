{-# LANGUAGE OverloadedStrings #-}
module Tau.EvalTests where

import Data.Maybe (fromJust, isNothing)
import Tau.Eval
import Tau.Expr
import Tau.Patterns
import Tau.Value
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testValueEnv :: ValueEnv Eval
testValueEnv = Env.fromList
    [ ("Cons"   , saturate "Cons" 2)
    , ("Nil"    , saturate "Nil" 0) 
    , ("Tuple2" , saturate "Tuple2" 2)
    , ("fst"    , evald (lamS "p" (matchS (varS "p") [(conP "Tuple2" [varP "a", varP "b"], varS "a")])))
    , ("snd"    , evald (lamS "p" (matchS (varS "p") [(conP "Tuple2" [varP "a", varP "b"], varS "b")])))
    ]

evald :: Expr -> Value Eval
evald expr = fromJust (evalExpr expr mempty)

failEval :: Expr -> SpecWith ()
failEval expr =
    describe ("The expression " <> prettyString expr) $ 
        it "✗ fails to evaluate" $
            isNothing (evalExpr (compileAll expr) testValueEnv)

succeedEval :: Expr -> Value Eval -> SpecWith ()
succeedEval expr val = 
    describe ("The expression " <> prettyString expr) $ 
        it ("✔ evaluates to the value " <> prettyString val) $
            evalExpr (compileAll expr) testValueEnv == Just val

isFunction :: Value Eval -> Bool
isFunction value = 
    case value of
        Closure{} -> True
        _ -> False

succeedEvalFunction :: Expr -> SpecWith ()
succeedEvalFunction expr =
    describe ("The expression " <> prettyString expr) $ 
        it "✔ evaluates to a function closure" $
            Just True == (isFunction <$> evalExpr (compileAll expr) testValueEnv)

testEval :: SpecWith ()
testEval = do
    succeedEval 
        (appS [lamS "x" (matchS (varS "x") [(litP (Int 3), litInt 1), (varP "x", varS "x")]), litInt 3])
        (Value (Int 1))

    succeedEval 
        (appS [lamS "x" (matchS (varS "x") [(litP (Int 3), litInt 1), (varP "x", varS "x")]), litInt 5])
        (Value (Int 5))

    succeedEval 
        (appS [lamMatchS [(litP (Int 3), litInt 1), (varP "x", varS "x")], litInt 3])
        (Value (Int 1))

    succeedEval 
        (appS [lamMatchS [(litP (Int 3), litInt 1), (varP "x", varS "x")], litInt 5])
        (Value (Int 5))

    succeedEvalFunction
        (lamS "a" (lamS "b" (varS "a")))

    succeedEvalFunction
        (letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit]))

    succeedEval 
        (letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5]))
        (Value Unit)

    succeedEval 
        (appS [lamS "xs" (matchS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Cons", litInt 5, appS [varS "Nil"]]])
        (Value (Int 1))

    succeedEval 
        (appS [lamS "xs" (matchS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Cons", litInt 5, varS "Nil"]])
        (Value (Int 1))

    succeedEval 
        (appS [lamMatchS [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)], appS [varS "Cons", litInt 5, appS [varS "Nil"]]])
        (Value (Int 1))

    succeedEval 
        (appS [lamS "xs" (matchS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Nil"]])
        (Value (Int 2))

    succeedEval 
        (letS "plus" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (letS "plus5" (appS [varS "plus", litInt 5]) (letS "id" (lamS "x" (varS "x")) (appS [appS [varS "id", varS "plus5"], appS [varS "id", litInt 3]]))))
        (Value (Int 8))

    succeedEval 
        (letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (addS (appS [varS "fst", varS "x", varS "snd", varS "x"]) (litInt 1))))
        (Value (Int 5))

    succeedEvalFunction
        (letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (appS [varS "fst", varS "x"])))

    failEval 
        (letS "x" (varS "x") (varS "x"))

    failEval 
        (letS "f" (lamS "n" (ifS (varS "n" `eqS` litInt 0) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5]))

    succeedEval 
        (recS "f" (lamS "n" (ifS (varS "n" `eqS` litInt 0) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5]))
        (Value (Int 120))

    failEval 
        (varS "hello")

    succeedEval 
        (appS [lamS "x" (matchS (varS "x") [(litP (Int 1), litInt 2), (litP (Int 2), litInt 3)]), litInt 1])
        (Value (Int 2))

    failEval 
        (letS "f" (lamS "n" (ifS (eqS (varS "n") (litInt 0)) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5]))

    succeedEval 
        (recS "f" (lamS "n" (ifS (eqS (varS "n") (litInt 0)) (litInt 1) (mulS (varS "n") (appS [varS "f", subS (varS "n") (litInt 1)])))) (appS [varS "f", litInt 5]))
        (Value (Int 120))

    succeedEval 
        (recS "length" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], litInt 0), (conP "Cons" [varP "x", varP "xs"], addS (litInt 1) (appS [varS "length", varS "xs"]))])) (appS [varS "length", appS [varS "Cons", litInt 1, appS [varS "Cons", litInt 1, appS [varS "Nil"]]]]))
        (Value (Int 2))

    succeedEval 
        (recS "length" (lamMatchS [(conP "Nil" [], litInt 0), (conP "Cons" [varP "x", varP "xs"], addS (litInt 1) (appS [varS "length", varS "xs"]))]) (appS [varS "length", appS [varS "Cons", litInt 1, appS [varS "Cons", litInt 1, appS [varS "Nil"]]]]))
        (Value (Int 2))

    succeedEval 
        (recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], varS "Nil"), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (appS [varS "map", lamS "x" (eqS (varS "x") (litInt 1)), appS [varS "Cons", litInt 1, appS [varS "Cons", litInt 2, appS [varS "Cons", litInt 3, varS "Nil"]]]]))
        (Data "Cons" [Value (Bool True), Data "Cons" [Value (Bool False), Data "Cons" [Value (Bool False), Data "Nil" []]]])

    succeedEval 
        (recS "map" (lamS "f" (lamMatchS [(conP "Nil" [], varS "Nil"), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])])) (appS [varS "map", lamS "x" (eqS (varS "x") (litInt 1)), appS [varS "Cons", litInt 1, appS [varS "Cons", litInt 2, appS [varS "Cons", litInt 3, varS "Nil"]]]]))
        (Data "Cons" [Value (Bool True), Data "Cons" [Value (Bool False), Data "Cons" [Value (Bool False), Data "Nil" []]]])
