{-# LANGUAGE OverloadedStrings #-}
module Tau.TestInfer where

import Data.Functor.Const
import Data.Functor.Foldable
import Data.Text (Text, pack, unpack)
import Tau.Ast
import Tau.Pattern
import Tau.Prim
import Tau.Type
import Tau.Type.Infer
import Tau.Type.Infer.Monad
import Tau.Type.TypedAst
import Tau.Util
import Test.Hspec
import Utils
import qualified Data.Map.Strict as Map
import qualified Utils.Pretty as Pretty

test010 :: Expr
test010 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit])

test011 :: Expr
test011 = appS [varS "const", litInt 5, litUnit]

test012 :: Expr
test012 = appS [varS "foo", litInt 5]

test013 :: Expr
test013 = appS [varS "Foo", litInt 5]

test014 :: Expr
test014 = lamS "a" (varS "a")

test015 :: Expr
test015 = lamS "a" (lamS "b" (varS "a"))

test020 :: Expr
test020 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5])

test030 :: Expr
test030 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses =
        [ (conP "Cons" [varP "y", varP "ys"], litInt 1)
        , (conP "Nil" [], litInt 2) ]

-- \xs -> case xs of { _ => 1 } Cons 5 Nil
test031 :: Expr
test031 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (anyP, litInt 1) ]

-- \xs -> case xs of { x => 1 } Cons 5 Nil
test032 :: Expr
test032 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (varP "x", litInt 1) ]

-- \xs -> case xs of { Cons y ys => 1 } Cons 5 Nil
test033 :: Expr
test033 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]
  where
    clauses = [ (conP "Cons" [varP "y", varP "ys"], litInt 1) ]

test034 :: Expr
test034 = letS "xs" (appS [varS "Baz"]) (caseS (varS "xs") [ (conP "Baz" [], litString "hello")])

test040 :: Expr
test040 = appS [lamS "xs" (caseS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Nil"]]

test041 :: Expr
test041 = appS [varS "Cons", litInt 5]

test042 :: Expr
test042 = appS [varS "Cons", litInt 5, appS [varS "Nil"]]

test043 :: Expr
test043 = appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]

test044 :: Expr
test044 = appS [varS "Cons", litInt 5, appS [varS "Cons", litBool True, appS [varS "Nil"]]]

-- case Cons 5 Nil of { Cons y ys -> y + 1; Nil -> 0 })
test050 :: Expr
test050 = caseS (appS [varS "Cons", litInt 5, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1))), (conP "Nil" [], litInt 0)]

-- case Cons "a" Nil of { Cons y ys -> y + 1 })
test053 :: Expr
test053 = caseS (appS [varS "Cons", litString "a", appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))]

-- case Cons 6 Nil of { Cons y ys -> y + 1 })
test054 :: Expr
test054 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))]

test055 :: Expr
test055 = letS "xs" (appS [varS "Cons", litBool True, appS [varS "Nil"]]) (letS "ys" (appS [varS "Cons", litInt 1, appS [varS "Nil"]]) (litInt 5))

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons 4 ys -> 5 })
test056 :: Expr
test056 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]]) [(conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1))), (conP "Cons" [litP (Int 4), varP "ys"], litInt 5)]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons 4 ys -> "foo" })
test057 :: Expr
test057 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [litP (Int 4), varP "ys"], litString "foo") ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; 5 -> 1 })
test058 :: Expr
test058 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (litP (Int 5), litInt 1) ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons "w" z -> 1 })
test059 :: Expr
test059 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [litP (String "w"), varP "z"], litInt 1) ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons z 5 -> 1 })
test060 :: Expr
test060 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], opS (AddS (varS "y") (litInt 1)))
    , (conP "Cons" [varP "z", litP (Int 5)], litInt 1) ]

-- case Cons 6 Nil of { Cons y ys -> "one"; _ -> "two" })
test061 :: Expr
test061 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], litString "one")
    , (anyP, litString "two") ]

-- case Cons 6 Nil of { Cons y ys -> y; _ -> "two" })
test062 :: Expr
test062 = caseS (appS [varS "Cons", litInt 6, appS [varS "Nil"]])
    [ (conP "Cons" [varP "y", varP "ys"], varS "y")
    , (anyP, litString "two") ]

-- case Nil of {}
test063 :: Expr
test063 = caseS (appS [varS "Nil"]) []

-- if 1 == True then 1 else 0
test070 :: Expr
test070 = ifS (eqS (litInt 1) (litBool True)) (litInt 1) (litInt 0)

-- if Cons True Nil == Cons 1 Nil then 1 else 0
test075 :: Expr
test075 = ifS (eqS (appS [varS "Cons", litBool True, appS [varS "Nil"]]) (appS [varS "Cons", litInt 1, appS [varS "Nil"]])) (litInt 1) (litInt 0)

test080 :: Expr
test080 = letS "plus" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (letS "plus5" (appS [varS "plus", litInt 5]) (letS "id" (lamS "x" (varS "x")) (appS [appS [varS "id", varS "plus5"], appS [varS "id", litInt 3]])))

-- let id = \x -> x in let x = (id, 4) in (fst x) (snd x) + 1
test090 :: Expr
test090 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (addS (appS [varS "fst", varS "x", varS "snd", varS "x"]) (litInt 1)))

test100 :: Expr
test100 = letS "x" (varS "x") (varS "x")

listA :: Type
listA = TApp (TCon "List") (TVar "a")

tuple2AB :: Type
tuple2AB = TApp (TApp (TCon "Tuple2") (TVar "a")) (TVar "b")

testContext :: Context
testContext = Context (Map.fromList
    [ ("Nil"    , Forall ["a"] listA)
    , ("Cons"   , Forall ["a"] (TArr (TVar "a") (TArr listA listA)))
    , ("const"  , Forall ["a", "b"] (TArr (TVar "a") (TArr (TVar "b") (TVar "a"))))
    , ("foo"    , Forall ["a"] (TArr (TVar "a") (TVar "a")))
    , ("Foo"    , Forall ["a"] (TArr (TVar "a") (TApp (TCon "List") (TVar "a"))))
    , ("Baz"    , Forall [] tBool)
    , ("Tuple2" , Forall ["a", "b"] (TArr (TVar "a") (TArr (TVar "b") tuple2AB)))
    , ("fst"    , Forall ["a", "b"] (TArr tuple2AB (TVar "a")))
    , ("snd"    , Forall ["a", "b"] (TArr tuple2AB (TVar "b")))
    ])

testInfer :: SpecWith ()
testInfer = do
    testSuccess
        (test010, Context mempty) (TVar "a" `TArr` tUnit) "test010"

    testFailure
        (test010, Context mempty) (TVar "a" `TArr` tInt) "test010"

    testSuccess
        (test011, testContext) tInt "test011"

    testFailure
        (test011, testContext) tBool "test011"

    testSuccess
        (test012, testContext) tInt "test012"

    testSuccess
        (test013, testContext) (TApp (TCon "List") tInt) "test013"

    testFailure
        (test013, testContext) (TApp (TCon "List") (TVar "a")) "test013"

    testSuccess
        (test014, Context mempty) (TVar "a" `TArr` TVar "a") "test014"

    testSuccess
        (test015, Context mempty) (TVar "a" `TArr` (TVar "b" `TArr` TVar "a")) "test015"

    testFailure
        (test015, Context mempty) (TVar "a" `TArr` (TVar "b" `TArr` TVar "b")) "test015"

    testFailure
        (test015, Context mempty) (TVar "b" `TArr` (TVar "b" `TArr` TVar "a")) "test015"

    testSuccess
        (test020, testContext) tUnit "test020"

    testSuccess
        (test030, testContext) tInt "test030"

    testSuccess
        (test031, testContext) tInt "test031"

    testSuccess
        (test032, testContext) tInt "test032"

    testSuccess
        (test033, testContext) tInt "test033"

    testSuccess
        (test034, testContext) tString "test034"

    testFailWithError
        (test053, testContext) CannotUnify "test053"

    testSuccess
        (test054, testContext) tInt "test054"

    testSuccess
        (test055, testContext) tInt "test055"

    testSuccess
        (test056, testContext) tInt "test056"

    testFailWithError
        (test057, testContext) CannotUnify "test057"

    testFailWithError
        (test058, testContext) CannotUnify "test058"

    testFailWithError
        (test059, testContext) CannotUnify "test059"

    testFailWithError
        (test060, testContext) CannotUnify "test060"

    testSuccess
        (test061, testContext) tString "test061"

    testFailWithError
        (test062, testContext) CannotUnify "test062"

    testFailWithError
        (test063, testContext) EmptyCaseStatement "test063"

    testFailWithError
        (test070, testContext) CannotUnify "test070"

    testFailWithError
        (test075, testContext) CannotUnify "test075"

    testSuccess
        (test080, testContext) tInt "test080"

    testSuccess
        (test090, testContext) tInt "test090"

    testFailWithError
        (test100, testContext) (UnboundVariable "x") "test100"

testSuccess :: (Expr, Context) -> Type -> Text -> SpecWith ()
testSuccess (expr, context) ty name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> Pretty.expr expr

    describeSuccess = unpack $
        "✔ has type ("
            <> Pretty._type ty
            <> ")"

    describeFailure = unpack $
        "Expected type to be identical to "
            <> "(" <> Pretty._type ty <> ")"
            <> " (up to isomorphism)"

    test = case runTest context expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            pass

        _ ->
            expectationFailure describeFailure

testFailure :: (Expr, Context) -> Type -> Text -> SpecWith ()
testFailure (expr, context) ty name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> Pretty.expr expr

    describeSuccess = unpack $
        "✗ does not have type ("
            <> Pretty._type ty
            <> ")"

    describeFailure = unpack $
        "Expected type NOT to be identical to "
            <> "(" <> Pretty._type ty <> ")"

    test = case runTest context expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            expectationFailure describeFailure

        _ ->
            pass

testFailWithError :: (Expr, Context) -> InferError -> Text -> SpecWith ()
testFailWithError (expr, context) err name =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> Pretty.expr expr

    describeSuccess = "✗ fails with error " <> show err

    test = case runTest context expr of
        Left e | err == e ->
            pass

        _ ->
            expectationFailure ("Expected test to fail with error " <> show err)

runTest :: Context -> Expr -> Either InferError Type
runTest context expr =
    getConst . left . unfix . runTypedExpr <$> errorOrTypedExpr
  where
    errorOrTypedExpr = runInfer (inferType context expr)
