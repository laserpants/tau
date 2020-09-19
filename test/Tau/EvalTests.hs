{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.EvalTests where

import Data.Maybe (fromJust, isNothing)
import Tau.Eval
import Tau.Expr
import Tau.Patterns
import Tau.Util.TH
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
    , ("fst"    , evald $(parseExpr "\\match (a, b) => a"))
    , ("snd"    , evald $(parseExpr "\\match (a, b) => b"))
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
        $(parseExpr "(\\x => match x with 3 => 1 | x => x) 3")
        (Value (Int 1))

    succeedEval
        $(parseExpr "(\\x => match x with | 3 => 1 | x => x) 5")
        (Value (Int 5))

    succeedEval
        $(parseExpr "(\\match | 3 => 1 | x => x) 3")
        (Value (Int 1))

    succeedEval
        $(parseExpr "(\\match 3 => 1 | x => x) 5")
        (Value (Int 5))

    succeedEvalFunction
        $(parseExpr "(\\a => \\b => a)")

    succeedEvalFunction
        $(parseExpr "let const = \\a => \\b => a in const ()")

    succeedEvalFunction
        $(parseExpr "let const a b = a in const ()")

    succeedEval
        $(parseExpr "let const = \\a => \\b => a in const () 5")
        (Value Unit)

    succeedEval
        $(parseExpr "let const = \\a b => a in const () 5")
        (Value Unit)

    succeedEval
        $(parseExpr "let const a b = a in const () 5")
        (Value Unit)

    succeedEval
        $(parseExpr "(\\xs => match xs with Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        (Value (Int 1))

    succeedEval
        $(parseExpr "(\\xs => match xs with Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        (Value (Int 1))

    succeedEval
        $(parseExpr "(\\match Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        (Value (Int 1))

    succeedEval
        $(parseExpr "(\\xs => match xs with | Cons y ys => 1 | Nil => 2) Nil")
        (Value (Int 2))

    succeedEval
        $(parseExpr "let plus = \\a => \\b => a + b in let plus5 = plus 5 in let id = \\x => x in (id plus5) (id 3)")
        (Value (Int 8))

    succeedEval
        $(parseExpr "let plus a b = a + b in let plus5 = plus 5 in let id x = x in (id plus5) (id 3)")
        (Value (Int 8))

    succeedEval
        $(parseExpr "let id = \\x => x in let x = Tuple2 id 4 in (fst x snd x) + 1")
        (Value (Int 5))

    succeedEval
        $(parseExpr "let id = \\x => x in let x = (id, 4) in (fst x snd x) + 1")
        (Value (Int 5))

    succeedEvalFunction
        $(parseExpr "let id = \\x => x in let x = Tuple2 id 4 in fst x")

    succeedEvalFunction
        $(parseExpr "let id = \\x => x in let x = (id, 4) in fst x")

    failEval
        $(parseExpr "let x = x in x")

    failEval
        $(parseExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")

    succeedEval
        $(parseExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
        (Value (Int 120))

    failEval
        (varS "hello")

    succeedEval
        $(parseExpr "(\\x => match x with 1 => 2 | 2 => 3) 1")
        (Value (Int 2))

    failEval
        $(parseExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")

    succeedEval
        $(parseExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
        (Value (Int 120))

    succeedEval
        $(parseExpr "let rec length = \\xs => match xs with Nil => 0 | Cons x xs => 1 + (length xs) in length (Cons 1 (Cons 1 Nil))")
        (Value (Int 2))

    succeedEval
        $(parseExpr "let rec length = \\match Nil => 0 | Cons x xs => 1 + (length xs) in length (Cons 1 (Cons 1 Nil))")
        (Value (Int 2))

    succeedEval
        $(parseExpr "let rec map = \\f => \\xs => match xs with Nil => Nil | Cons x1 xs1 => Cons (f x1) (map f xs1) in map (\\x => x == 1) (Cons 1 (Cons 2 (Cons 3 Nil)))")
        (Data "Cons" [Value (Bool True), Data "Cons" [Value (Bool False), Data "Cons" [Value (Bool False), Data "Nil" []]]])

    succeedEval
        $(parseExpr "let rec map = \\f => \\match Nil => Nil | Cons x1 xs1 => Cons (f x1) (map f xs1) in map (\\x => x == 1) (Cons 1 (Cons 2 (Cons 3 Nil)))")
        (Data "Cons" [Value (Bool True), Data "Cons" [Value (Bool False), Data "Cons" [Value (Bool False), Data "Nil" []]]])

    succeedEval
        $(parseExpr "let fst = \\match | Tuple2 a _ => a in let rec length = \\match | Nil => 0 | Cons x xs => 1 + (length xs) in length (fst (Tuple2 (Cons 1 (Cons 2 (Cons 3 Nil))) 5))")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | Cons x xs => 1 + (length xs) in length (fst (Tuple2 (Cons 1 (Cons 2 (Cons 3 Nil))) 5))")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | Cons x xs => 1 + (length xs) in length (fst (1 :: 2 :: 3 :: [], 5))")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | Cons x xs => 1 + (length xs) in length (fst ([1, 2, 3], 5))")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in length (fst ([1,2,3], 5))")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in (fst ([1,2,3], 5)).length")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in (([1,2,3], 5).fst).length")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let fst = \\match | (a, _) => a in let rec length = \\match | Nil => 0 | x::xs => 1 + (length xs) in ([1,2,3], 5).fst.length")
        (Value (Int 3))

    succeedEval
        $(parseExpr "let f = \\match (a, b) => a in let rec g = \\match [] => 0 | x::xs => g xs + 1 in let h = \\x => x + 1 in h (g (f ([1,2,3], 4)))")
        (Value (Int 4))

    succeedEval
        $(parseExpr "let f = \\match (a, b) => a in let rec g = \\match [] => 0 | x::xs => g xs + 1 in let h = \\x => x + 1 in let z = h << g << f in z ([1,2,3], 4)")
        (Value (Int 4))

    succeedEval
        $(parseExpr "let f (a, b) = a in let rec g = \\match [] => 0 | x::xs => g xs + 1 in let h x = x + 1 in let z = h << g << f in z ([1,2,3], 4)")
        (Value (Int 4))

    succeedEval
        $(parseExpr "let f (a, b) = a in let rec g = \\match [] => 0 | x::xs => g xs + 1 in let h x = x + 1 in let z = h << (g << f) in z ([1,2,3], 4)")
        (Value (Int 4))

    succeedEval
        $(parseExpr "let fst = \\match (a, b) => a in fst (1, 2)")
        (Value (Int 1))

    succeedEval
        $(parseExpr "let fst = \\match (a, b) => a in (1, 2).fst")
        (Value (Int 1))

    succeedEval
        $(parseExpr "let fst (a, b) = a in (1, 2).fst")
        (Value (Int 1))

    succeedEval
        $(parseExpr "(\\x y z => x + z) 2 3 4")
        (Value (Int 6))

    succeedEval
        $(parseExpr "(\\() => 5) ()")
        (Value (Int 5))

    succeedEval
        $(parseExpr "(\\() => ()) ()")
        (Value Unit)

    succeedEval
        $(parseExpr "let number = \\_ => 42 in (4, 4).number")
        (Value (Int 42))

    succeedEval
        $(parseExpr "let number = \\_ => 42 in { number = 42 }.number")
        (Value (Int 42))

    succeedEval
        $(parseExpr "match { a = 5 } with { a = 3 } => 0 | _ => 1")
        (Value (Int 1))

    succeedEval
        $(parseExpr "match { a = 5 } with { a = x } => x | _ => 1")
        (Value (Int 5))

    succeedEval
        $(parseExpr "match Tuple2 100 1 with Tuple2 x 1 => x | _ => 1")
        (Value (Int 100))

    succeedEval
        $(parseExpr "match Tuple2 100 1 with Tuple2 101 1 => x | _ => 1")
        (Value (Int 1))

    succeedEval
        $(parseExpr "match Tuple2 100 2 with Tuple2 x y => y | _ => 1")
        (Value (Int 2))

    succeedEval
        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, c = name } => (x, name) | _ => (0, \"default\")")
        (Data "Tuple2" [Value (Int 5), Value (String "hello")])




--    failEval 
--        $(parseExpr "match Tuple2 100 2 with Tuple2 x x => y | _ => 1")

--    succeedEval
--        $(parseExpr "{ number = 42 }.number")
--        (Value (Int 42))
--
--    succeedEval
--        $(parseExpr "let plus1 x = x + 1 in { number = 42 }.number.plus1")
--        (Value (Int 43))
--
--    succeedEval
--        $(parseExpr "let info = { number = 42 } in info.number")
--        (Value (Int 42))
