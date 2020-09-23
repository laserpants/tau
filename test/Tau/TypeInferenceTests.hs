{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.TypeInferenceTests where

import Tau.Env (Env(..))
import Tau.Expr
import Tau.Solver
import Tau.Type
import Tau.Patterns
import Tau.Type.Inference
import Tau.Util.TH
import Test.Hspec
import Utils
import qualified Tau.Env.Builtin as Builtin
import qualified Tau.Env as Env

testTypeEnv :: Env Scheme
testTypeEnv = Env.fromList
    [ ( "concat" , $(parseScheme "String -> String -> String") )
    , ( "show"   , $(parseScheme "forall a. (Show a) => a -> String") )
    , ( "Nil"    , $(parseScheme "forall a. List a") )
    , ( "Cons"   , $(parseScheme "forall a. a -> List a -> List a") )
    , ( "const"  , $(parseScheme "forall a b. a -> b -> a") )
    , ( "foo"    , $(parseScheme "forall a. a -> a") )
    , ( "Foo"    , $(parseScheme "forall a. a -> List a") )
    , ( "fst"    , $(parseScheme "forall a b. (a, b) -> a") )
    , ( "snd"    , $(parseScheme "forall a b. (a, b) -> b") )
    , ( "Baz"    , $(parseScheme "Bool") )
    , ( "equals" , $(parseScheme "forall a. (Eq a) => a -> a -> Bool") )
    , ( "plus"   , $(parseScheme "forall a. (Num a) => a -> a -> a") )
    , ( "Show"   , $(parseScheme "forall a. a -> String -> Show a") )
    ]

runTest :: Expr -> Either TypeError (Type, [TyClass])
runTest expr = do
    (ty, sub, tycls) <- runInferType (Builtin.typeSchemes `Env.union` testTypeEnv) expr
    pure (apply sub ty, apply sub <$> tycls)

result :: Expr -> Either TypeError Scheme
result expr = normalize . generalize mempty [] . fst <$> runTest expr

succeedInferType :: Expr -> Scheme -> SpecWith ()
succeedInferType expr expected =
    describe ("The expression : " <> prettyString expr) $
        it ("✔ has type " <> prettyString expected) $
            result expr == Right (normalize expected)

failInferTypeWithError :: TypeError -> Expr -> SpecWith ()
failInferTypeWithError err expr =
    describe ("The expression : " <> prettyString expr) $
        it ("✗ fails with error " <> show err) $
            result expr == Left err

testTypeInference :: SpecWith ()
testTypeInference = do
    succeedInferType
        $(parseExpr "let const = \\a => \\b => a in const ()")
        $(parseScheme "forall a. a -> Unit")

    succeedInferType
        $(parseExpr "const 5 ()")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "foo 5")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "Foo 5")
        $(parseScheme "List Int")

    succeedInferType
        $(parseExpr "\\a => a")
        $(parseScheme "forall a. a -> a")

    succeedInferType
        $(parseExpr "\\a => \\b => a")
        $(parseScheme "forall a b. a -> b -> a")

    succeedInferType
        $(parseExpr "\\a => \\b => a")
        $(parseScheme "forall a b. a -> (b -> a)")

    succeedInferType
        $(parseExpr "let const = \\a => \\b => a in const () 5")
        $(parseScheme "Unit")

    succeedInferType
        $(parseExpr "let const = \\a => \\_ => a in const () 5")
        $(parseScheme "Unit")

    succeedInferType
        $(parseExpr "(\\xs => match xs with Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "(\\match Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "\\match Cons y ys => 1 | Nil => 2")
        $(parseScheme "forall a. List a -> Int")

    succeedInferType
        $(parseExpr "(\\xs => match xs with _ => 1) (Cons 5 Nil)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "(\\xs => match xs with x => 1) (Cons 5 Nil)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "(\\xs => match xs with Cons y ys => 1) (Cons 5 Nil)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "let xs = Baz in match xs with Baz => \"hello\"")
        $(parseScheme "String")

    succeedInferType
        $(parseExpr "(\\xs => match xs with | Cons y ys => 1 | Nil => 2) Nil")
        $(parseScheme "Int")

    succeedInferType
        (appS [lamMatchS [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)], appS [varS "Nil"]])
        $(parseScheme "Int")

    succeedInferType
        (appS [lamMatchS [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)], varS "Nil"])
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "let xs = Cons True Nil in let ys = Cons 1 Nil in 5")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons 4 ys => 5")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "match Cons 6 Nil with Cons y ys => \"one\" | _ => \"two\"")
        $(parseScheme "String")

    succeedInferType
        $(parseExpr "let plus = \\a => \\b => a + b in let plus5 = plus 5 in let id = \\x => x in (id plus5) (id 3)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "let id = \\x => x in let x = (id, 4) in (fst x snd x) + 1")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "(\\x => match x with 1 => 2 | 2 => 3) 1")
        $(parseScheme "Int")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match Cons \"a\" Nil with Cons y ys => y + 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons 4 ys => \"foo\"")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | 5 => 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons \"w\" z => 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons z 5 => 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match Cons 6 Nil with Cons y ys => y | _ => \"two\"")

    failInferTypeWithError EmptyMatchStatement
        (matchS (appS [varS "Nil"]) [])

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == True then 1 else 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if Cons True Nil == Cons 1 Nil then 1 else 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if Cons True Nil == Foo 1 Nil then 1 else 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if Cons True Nil == Cons then 1 else 0")

    failInferTypeWithError (UnboundVariable "x")
        $(parseExpr "let x = x in x")

    failInferTypeWithError (UnboundVariable "f")
        $(parseExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")

    succeedInferType
        $(parseExpr "let fst = \\match (a, b) => a in fst (1, 2)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "let fst = \\match (a, b) => a in (1, 2).fst")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "let fst (a, b) = a in fst (1, 2)")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "(\\x y z => x + z)")
        $(parseScheme "forall a b. a -> b -> a -> a")

    failInferTypeWithError (NameClash "key")
        $(parseExpr "let key = \\_ => 5 in { key = 5 }.key")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == 1 then (1, 2) else (1,2,3)")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == 1 then (1, 2) else (1,'a')")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == 1 then 1 :: 2 :: [] else False :: []")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "1 :: False :: []")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == 1 then { a = 3 } else { a = 3, b = 3 }")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == 1 then { a = 3 } else { a = False }")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "if 1 == 1 then { a = 3 } else { b = 3 }")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match { a = 3 } with { a = 3 } => 0 | { a = 4, b = 5 } => 0 | _ => 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match { a = 3 } with { a = 3 } => 0 | { b = 4 } => 0 | _ => 0")

    failInferTypeWithError (UnificationError CannotUnify)
        (compileAll $(parseExpr "match (1, 2) with (2, 3) => 0 | (2, 3, 4) => 0 | _ => 0"))

    failInferTypeWithError (UnificationError CannotUnify)
        (compileAll $(parseExpr "match (1, 2) with (2, 3) => 0 | (\"a\", 3) => 0 | _ => 0"))

    succeedInferType
        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, c = name } => (x, name) | _ => (0, \"default\")")
        $(parseScheme "(Int, String)")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, c = name } => (x, x) | _ => (0, \"default\")")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match { a = 5, b = 'a', c = \"hello\" } with { a = x, b = _, d = name } => (x, name) | _ => (0, \"default\")")

    failInferTypeWithError (UnboundVariable "x")
        $(parseExpr "match (100, 1) with (101, 1) => x | _ => 1")

    succeedInferType
        $(parseExpr "match { stuff = (), user = { name = \"Bob\" } } with { stuff = (), user = { name = name } } => name")
        $(parseScheme "String")

    succeedInferType
        $(parseExpr "match { stuff = (), user = { id = 1, name = \"Bob\" } } with { stuff = (), user = { id = _, name = name } } => name")
        $(parseScheme "String")

    succeedInferType
        $(parseExpr "match { stuff = (), user = { id = 1, data = { name = \"Bob\", shoeSize = 42 } } } with { stuff = (), user = { id = _, data = { name = name, shoeSize = 42 } } } => name")
        $(parseScheme "String")

    succeedInferType
        $(parseExpr "match { stuff = (), user = { id = 1, data = { name = (\"Bob\", \"Doe\"), shoeSize = 42 } } } with { stuff = (), user = { id = _, data = { name = (firstName, _), shoeSize = 42 } } } => firstName")
        $(parseScheme "String")

    failInferTypeWithError (UnificationError CannotUnify)
        $(parseExpr "match { a = 5 } with { a = x, b = _ } => 1 | _ => 123")

    succeedInferType
        $(parseExpr "let fst (a, b) = a in { a = { b = ({ stuff = ['x', 'y'] }, 3) } }.a.b.fst.stuff")
        $(parseScheme "List Char")

    succeedInferType
        $(parseExpr "let x = { a = { b = \\() => 123 } } in x.a.b ()")
        $(parseScheme "Int")

    succeedInferType
        $(parseExpr "((\\{ x = y } => { z = y }) { x = \"stuff\" }).z")
        $(parseScheme "String")

--    succeedInferType
--        $(parseExpr "{ key = 5 }.key")
--        $(parseScheme "Int")
--
--    succeedInferType
--        $(parseExpr "let obj = { key = 5 } in obj.key")
--        $(parseScheme "Int")
--
--    failInferTypeWithError (UnboundVariable "b")
--        $(parseExpr "{ a = 5 }.b")
--
--    succeedInferType
--        $(parseExpr "{ a = { b = 5 }}.a.b")
--        $(parseScheme "Int")
--
--    succeedInferType
--        $(parseExpr "{ a = { a = \"test\" }}.a.a")
--        $(parseScheme "String")
--
--    failInferTypeWithError (UnboundVariable "a")
--        $(parseExpr "{ a = { b = 3 } }.a.a")
