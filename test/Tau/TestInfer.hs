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
test010 = letS [("const", lamS "a" (lamS "b" (varS "a")))] (appS [varS "const", litS Unit])

test011 :: Expr
test011 = appS [varS "const", litS (Int 5), litS Unit]

test012 :: Expr
test012 = appS [varS "foo", litS (Int 5)]

test013 :: Expr
test013 = appS [varS "Foo", litS (Int 5)]

test014 :: Expr
test014 = lamS "a" (varS "a")

test015 :: Expr
test015 = lamS "a" (lamS "b" (varS "a"))

test020 :: Expr
test020 = letS [("const", lamS "a" (lamS "b" (varS "a")))] (appS [varS "const", litS Unit, litS (Int 5)])

test030 :: Expr
test030 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litS (Int 5), appS [varS "Nil"]]]
  where
    clauses =
        [ (ConP "Cons" [VarP "y", VarP "ys"], litS (Int 1))
        , (ConP "Nil" [], litS (Int 2)) ]

-- \xs -> case xs of { _ => 1 } Cons 5 Nil
test031 :: Expr
test031 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litS (Int 5), appS [varS "Nil"]]]
  where
    clauses = [ (AnyP, litS (Int 1)) ]

-- \xs -> case xs of { x => 1 } Cons 5 Nil
test032 :: Expr
test032 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litS (Int 5), appS [varS "Nil"]]]
  where
    clauses = [ (VarP "x", litS (Int 1)) ]

-- \xs -> case xs of { Cons y ys => 1 } Cons 5 Nil
test033 :: Expr
test033 = appS [lamS "xs" (caseS (varS "xs") clauses), appS [varS "Cons", litS (Int 5), appS [varS "Nil"]]]
  where
    clauses = [ (ConP "Cons" [VarP "y", VarP "ys"], litS (Int 1)) ]

test034 :: Expr
test034 = letS [("xs", appS [varS "Baz"])] (caseS (varS "xs") [ (ConP "Baz" [], litS (String "hello"))])

test040 :: Expr
test040 = appS [lamS "xs" (caseS (varS "xs") [(ConP "Cons" [VarP "y", VarP "ys"], litS (Int 1)), (ConP "Nil" [], litS (Int 2))]), appS [varS "Nil"]]

test041 :: Expr
test041 = appS [varS "Cons", litS (Int 5)]

test042 :: Expr
test042 = appS [varS "Cons", litS (Int 5), appS [varS "Nil"]]

test043 :: Expr
test043 = appS [varS "Cons", litS (Int 5), appS [varS "Cons", litS (Int 4), appS [varS "Nil"]]]

test044 :: Expr
test044 = appS [varS "Cons", litS (Int 5), appS [varS "Cons", litS (Bool True), appS [varS "Nil"]]]

-- case Cons 5 Nil of { Cons y ys -> y + 1; Nil -> 0 })
test050 :: Expr
test050 = caseS (appS [varS "Cons", litS (Int 5), appS [varS "Nil"]]) [(ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1)))), (ConP "Nil" [], litS (Int 0))]

test0aa :: Expr
test0aa = ifS (eqS (litS (Int 1)) (litS (Bool True))) (litS (Int 1)) (litS (Int 0))

test0ab :: Expr
test0ab = ifS (eqS (appS [varS "Cons", litS (Bool True), appS [varS "Nil"]]) (appS [varS "Cons", litS (Int 1), appS [varS "Nil"]])) (litS (Int 1)) (litS (Int 0))

-- case Cons "a" Nil of { Cons y ys -> y + 1 })
test053 :: Expr
test053 = caseS (appS [varS "Cons", litS (String "a"), appS [varS "Nil"]]) [(ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1))))]

-- case Cons 6 Nil of { Cons y ys -> y + 1 })
test054 :: Expr
test054 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]]) [(ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1))))]

test055 :: Expr
test055 = letS
    [ ("xs", appS [varS "Cons", litS (Bool True), appS [varS "Nil"]])
    , ("ys", appS [varS "Cons", litS (Int 1), appS [varS "Nil"]])
    ] (litS (Int 5))

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons 4 ys -> 5 })
test056 :: Expr
test056 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]]) [(ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1)))), (ConP "Cons" [LitP (Int 4), VarP "ys"], litS (Int 5))]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons 4 ys -> "foo" })
test057 :: Expr
test057 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]])
    [ (ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1))))
    , (ConP "Cons" [LitP (Int 4), VarP "ys"], litS (String "foo")) ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; 5 -> 1 })
test058 :: Expr
test058 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]])
    [ (ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1))))
    , (LitP (Int 5), litS (Int 1))
    ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons "w" z -> 1 })
test059 :: Expr
test059 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]])
    [ (ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1))))
    , (ConP "Cons" [LitP (String "w"), VarP "z"], litS (Int 1)) ]

-- case Cons 6 Nil of { Cons y ys -> y + 1; Cons z 5 -> 1 })
test060 :: Expr
test060 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]])
    [ (ConP "Cons" [VarP "y", VarP "ys"], opS (AddS (varS "y") (litS (Int 1))))
    , (ConP "Cons" [VarP "z", LitP (Int 5)], litS (Int 1)) ]

-- case Cons 6 Nil of { Cons y ys -> "one"; _ -> "two" })
test061 :: Expr
test061 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]])
    [ (ConP "Cons" [VarP "y", VarP "ys"], litS (String "one"))
    , (AnyP, litS (String "two")) ]

-- case Cons 6 Nil of { Cons y ys -> y; _ -> "two" })
test062 :: Expr
test062 = caseS (appS [varS "Cons", litS (Int 6), appS [varS "Nil"]])
    [ (ConP "Cons" [VarP "y", VarP "ys"], varS "y")
    , (AnyP, litS (String "two")) ]

listA :: Type
listA = TApp (TCon "List") (TVar "a")

testContext :: Context
testContext = Context (Map.fromList
    [ ("Nil", Forall ["a"] listA)
    , ("Cons", Forall ["a"] (TArr (TVar "a") (TArr listA listA)))
    , ("const", Forall ["a", "b"] (TArr (TVar "a") (TArr (TVar "b") (TVar "a"))))
    , ("foo", Forall ["a"] (TArr (TVar "a") (TVar "a")))
    , ("Foo", Forall ["a"] (TArr (TVar "a") (TApp (TCon "List") (TVar "a"))))
    , ("Baz", Forall [] tBool)
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
