{-# LANGUAGE OverloadedStrings #-}
module Tau.TestTypeInterface where

import Data.Functor.Const
import Data.Functor.Foldable
import Data.Text (Text, pack, unpack)
import Tau.Ast
import Tau.Core
import Tau.Eval
import Tau.Prim
import Tau.Type
import Tau.Type.Infer
import Tau.Type.Infer.Monad
import Tau.Type.TypedAst
import Tau.Value
import Test.Hspec
import Utils
import qualified Data.Map.Strict as Map
import qualified Utils.Pretty as Pretty

-- show 123
test000 :: Expr
test000 = appS [varS "show", litInt 123]

-- show False
test010 :: Expr
test010 = appS [varS "show", litBool False]

-- show "abc"
test020 :: Expr
test020 = appS [varS "show", litString "abc"]

testTypeInterface :: SpecWith ()
testTypeInterface = do
    testEvalsTo (test000, Value (String "123"))   "test000"
    testHasType (test000, tString)                "test000"
    testEvalsTo (test010, Value (String "False")) "test010"
    testHasType (test010, tString)                "test010"
    testEvalsTo (test020, Value (String "abc"))   "test020"
    testHasType (test020, tString)                "test020"

testEvalsTo :: (Expr, Value Eval) -> Text -> SpecWith ()
testEvalsTo (expr, val) name =
    describe description (it describeSuccess test)
  where
    description = unpack $ name <> ": " <> Pretty.expr expr

    describeSuccess = unpack $ "✔ evaluates to " <> Pretty.value val

    test = case (runEvalTest expr, val) of
        (Left err, _) ->
            expectationFailure ("Unexpected error: " <> show err)

        (Right (Value v1), Value v2) | v1 == v2 ->
            pass

        (Right result, _) ->
            expectationFailure $ unpack ("Unexpected result: " <> Pretty.value result)

evalE :: Expr -> Value Eval
evalE expr = result where Right result = evalExpr mempty expr

testEnv :: Env Eval
testEnv = Map.fromList
    [ --("show" , undefined)
    ]

runEvalTest :: Expr -> Either EvalError (Value Eval)
runEvalTest = evalExpr testEnv

testHasType :: (Expr, Type) -> Name -> SpecWith ()
testHasType (expr, ty) name =
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

    test = case runInferTypeTest testContext expr of
        Left err ->
            expectationFailure ("Type inference error: " <> show err)

        Right ty' | isoTypes ty ty'  ->
            pass

        _ ->
            expectationFailure describeFailure

runInferTypeTest :: Context -> Expr -> Either InferError Type
runInferTypeTest context expr =
    getConst . left . unfix . runTypedExpr <$> errorOrTypedExpr
  where
    errorOrTypedExpr = runInfer (inferType context expr)

testContext :: Context
testContext = Context (Map.fromList
    [ ("show" , Forall ["a"] (TArr (TVar "a") tString))
    ])
