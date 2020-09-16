{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.EvalTests where

import Data.Maybe (fromJust, isNothing)
import TH
import Tau.Eval
import Tau.Expr
import Tau.Patterns
import Tau.Value
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testValueEnv :: ValueEnv Eval
testValueEnv = Env.fromList
    [ ("Cons"   , dataCon "Cons" 2)
    , ("Nil"    , dataCon "Nil" 0)
    , ("Tuple2" , dataCon "Tuple2" 2)
    , ("Tuple3" , dataCon "Tuple3" 3)
    , ("Tuple4" , dataCon "Tuple4" 4)
    , ("Tuple5" , dataCon "Tuple5" 5)
    , ("Tuple6" , dataCon "Tuple6" 6)
    , ("Tuple7" , dataCon "Tuple7" 7)
    , ("Tuple8" , dataCon "Tuple8" 8)
    , ("fst"    , evald $(mkExpr "\\match (a, b) => a"))
    , ("snd"    , evald $(mkExpr "\\match (a, b) => b"))
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
        $(mkExpr "(\\x => match x with 3 => 1 | x => x) 3")
        (Value (Int 1))

    succeedEval
        $(mkExpr "(\\x => match x with | 3 => 1 | x => x) 5")
        (Value (Int 5))

    succeedEval
        $(mkExpr "(\\match | 3 => 1 | x => x) 3")
        (Value (Int 1))

    succeedEval
        $(mkExpr "(\\match 3 => 1 | x => x) 5")
        (Value (Int 5))

    succeedEvalFunction
        $(mkExpr "(\\a => \\b => a)")

    succeedEvalFunction
        $(mkExpr "let const = \\a => \\b => a in const ()")

    succeedEval
        $(mkExpr "let const = \\a => \\b => a in const () 5")
        (Value Unit)

    succeedEval
        $(mkExpr "(\\xs => match xs with Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        (Value (Int 1))

    succeedEval
        $(mkExpr "(\\xs => match xs with Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        (Value (Int 1))

    succeedEval
        $(mkExpr "(\\match Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        (Value (Int 1))

    succeedEval
        $(mkExpr "(\\xs => match xs with | Cons y ys => 1 | Nil => 2) Nil")
        (Value (Int 2))

    succeedEval
        $(mkExpr "let plus = \\a => \\b => a + b in let plus5 = plus 5 in let id = \\x => x in (id plus5) (id 3)")
        (Value (Int 8))

    succeedEval
        $(mkExpr "let id = \\x => x in let x = Tuple2 id 4 in (fst x snd x) + 1")
        (Value (Int 5))

    succeedEvalFunction
        $(mkExpr "let id = \\x => x in let x = Tuple2 id 4 in fst x")

    failEval
        $(mkExpr "let x = x in x")

    failEval
        $(mkExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")

    succeedEval
        $(mkExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
        (Value (Int 120))

    failEval
        (varS "hello")

    succeedEval
        $(mkExpr "(\\x => match x with 1 => 2 | 2 => 3) 1")
        (Value (Int 2))

    failEval
        $(mkExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")

    succeedEval
        $(mkExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
        (Value (Int 120))

    succeedEval
        $(mkExpr "let rec length = \\xs => match xs with Nil => 0 | Cons x xs => 1 + (length xs) in length (Cons 1 (Cons 1 Nil))")
        (Value (Int 2))

    succeedEval
        $(mkExpr "let rec length = \\match Nil => 0 | Cons x xs => 1 + (length xs) in length (Cons 1 (Cons 1 Nil))")
        (Value (Int 2))

    succeedEval
        $(mkExpr "let rec map = \\f => \\xs => match xs with Nil => Nil | Cons x1 xs1 => Cons (f x1) (map f xs1) in map (\\x => x == 1) (Cons 1 (Cons 2 (Cons 3 Nil)))")
        (Data "Cons" [Value (Bool True), Data "Cons" [Value (Bool False), Data "Cons" [Value (Bool False), Data "Nil" []]]])

    succeedEval
        $(mkExpr "let rec map = \\f => \\match Nil => Nil | Cons x1 xs1 => Cons (f x1) (map f xs1) in map (\\x => x == 1) (Cons 1 (Cons 2 (Cons 3 Nil)))")
        (Data "Cons" [Value (Bool True), Data "Cons" [Value (Bool False), Data "Cons" [Value (Bool False), Data "Nil" []]]])

    succeedEval
        $(mkExpr "let fst = \\match | Tuple2 a _ => a in let rec length = \\match | Nil => 0 | Cons x xs => 1 + (length xs) in length (fst (Tuple2 (Cons 1 (Cons 2 (Cons 3 Nil))) 5))")
        (Value (Int 3))

    succeedEval
        $(mkExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in length (fst ([1,2,3], 5))")
        (Value (Int 3))

    succeedEval
        $(mkExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in (fst ([1,2,3], 5)).length")
        (Value (Int 3))

    succeedEval
        $(mkExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in ([1,2,3], 5).fst.length")
        (Value (Int 3))

    succeedEval
        $(mkExpr "let f = \\match (a, b) => a in let rec g = \\match [] => 0 | x::xs => g xs + 1 in let h = \\x => x + 1 in h (g (f ([1,2,3], 4)))")
        (Value (Int 4))

    succeedEval
        $(mkExpr "let f = \\match (a, b) => a in let rec g = \\match [] => 0 | x::xs => g xs + 1 in let h = \\x => x + 1 in let z = h ` g ` f in z ([1,2,3], 4)")
        (Value (Int 4))
