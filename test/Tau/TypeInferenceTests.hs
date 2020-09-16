{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.TypeInferenceTests where

import TH
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Solver
import Tau.Type
import Tau.Type.Inference
import Test.Hspec
import Utils
import qualified Tau.Env as Env

testTypeEnv :: Env Scheme
testTypeEnv = Env.fromList
    [ ( "concat" , $(mkScheme "String -> String -> String") )
    , ( "show"   , $(mkScheme "forall a. (Show a) => a -> String") )
    , ( "Nil"    , $(mkScheme "forall a. List a") )
    , ( "Cons"   , $(mkScheme "forall a. a -> List a -> List a") )
    , ( "const"  , $(mkScheme "forall a b. a -> b -> a") )
    , ( "foo"    , $(mkScheme "forall a. a -> a") )
    , ( "Foo"    , $(mkScheme "forall a. a -> List a") )
    , ( "Tuple2" , $(mkScheme "forall a b. a -> b -> Tuple2 a b") )
    , ( "fst"    , $(mkScheme "forall a b. Tuple2 a b -> a") )
    , ( "snd"    , $(mkScheme "forall a b. Tuple2 a b -> b") )
    , ( "Baz"    , $(mkScheme "Bool") )
    , ( "equals" , $(mkScheme "forall a. (Eq a) => a -> a -> Bool") )
    , ( "plus"   , $(mkScheme "forall a. (Num a) => a -> a -> a") )
    , ( "Show"   , $(mkScheme "forall a. a -> String -> Show a") )
    ]

runTest :: Expr -> Either TypeError (Type, [TyClass])
runTest expr = do
    (ty, sub, tycls) <- runInferType testTypeEnv expr
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
        $(mkExpr "let const = \\a => \\b => a in const ()")
        $(mkScheme "forall a. a -> Unit")

    succeedInferType
        $(mkExpr "const 5 ()")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "foo 5")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "Foo 5")
        $(mkScheme "List Int")

    succeedInferType
        $(mkExpr "\\a => a")
        $(mkScheme "forall a. a -> a")

    succeedInferType
        $(mkExpr "\\a => \\b => a")
        $(mkScheme "forall a b. a -> b -> a")

    succeedInferType
        $(mkExpr "\\a => \\b => a")
        $(mkScheme "forall a b. a -> (b -> a)")

    succeedInferType
        $(mkExpr "let const = \\a => \\b => a in const () 5")
        $(mkScheme "Unit")

    succeedInferType
        $(mkExpr "(\\xs => match xs with Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "(\\match Cons y ys => 1 | Nil => 2) (Cons 5 Nil)")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "\\match Cons y ys => 1 | Nil => 2")
        $(mkScheme "forall a. List a -> Int")

    succeedInferType
        $(mkExpr "(\\xs => match xs with _ => 1) (Cons 5 Nil)")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "(\\xs => match xs with x => 1) (Cons 5 Nil)")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "(\\xs => match xs with Cons y ys => 1) (Cons 5 Nil)")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "let xs = Baz in match xs with Baz => \"hello\"")
        $(mkScheme "String")

    succeedInferType
        $(mkExpr "(\\xs => match xs with | Cons y ys => 1 | Nil => 2) Nil")
        $(mkScheme "Int")

    succeedInferType
        (appS [lamMatchS [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)], appS [varS "Nil"]])
        $(mkScheme "Int")

    succeedInferType
        (appS [lamMatchS [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)], varS "Nil"])
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "match Cons 6 Nil with Cons y ys => y + 1")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "let xs = Cons True Nil in let ys = Cons 1 Nil in 5")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons 4 ys => 5")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "match Cons 6 Nil with Cons y ys => \"one\" | _ => \"two\"")
        $(mkScheme "String")

    succeedInferType
        $(mkExpr "let plus = \\a => \\b => a + b in let plus5 = plus 5 in let id = \\x => x in (id plus5) (id 3)")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "let id = \\x => x in let x = Tuple2 id 4 in (fst x snd x) + 1")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "let rec f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
        $(mkScheme "Int")

    succeedInferType
        $(mkExpr "(\\x => match x with 1 => 2 | 2 => 3) 1")
        $(mkScheme "Int")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "match Cons \"a\" Nil with Cons y ys => y + 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons 4 ys => \"foo\"")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "match Cons 6 Nil with Cons y ys => y + 1 | 5 => 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons \"w\" z => 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "match Cons 6 Nil with Cons y ys => y + 1 | Cons z 5 => 1")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "match Cons 6 Nil with Cons y ys => y | _ => \"two\"")

    failInferTypeWithError EmptyMatchStatement
        (matchS (appS [varS "Nil"]) [])

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "if 1 == True then 1 else 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "if Cons True Nil == Cons 1 Nil then 1 else 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "if Cons True Nil == Foo 1 Nil then 1 else 0")

    failInferTypeWithError (UnificationError CannotUnify)
        $(mkExpr "if Cons True Nil == Cons then 1 else 0")

    failInferTypeWithError (UnboundVariable "x")
        $(mkExpr "let x = x in x")

    failInferTypeWithError (UnboundVariable "f")
        $(mkExpr "let f = \\n => if n == 0 then 1 else n * (f (n - 1)) in f 5")
