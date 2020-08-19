{-# LANGUAGE OverloadedStrings #-}
module Tau.TestTypeInterface where

import Data.Functor.Const
import Data.Functor.Foldable
import Data.Text (Text, pack, unpack)
import Tau.Ast
import Tau.Core
import Tau.Eval
import Tau.Pattern
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

-- (\s -> \a -> case s of { Show f => f a }) (Show id) "hello"
-- "hello" : String
test000 :: Expr
test000 = appS [lamS "s" (lamS "a" (caseS (varS "s") [(conP "Show" [varP "f"], appS [varS "f", varS "a"])])), appS [varS "Show", varS "id"], litString "hello"]

-- (\s -> \a -> case s of { Show f => f a }) (Show (\x -> if x then "True" else "False")) False
-- "False" : String
test010 :: Expr
test010 = appS [lamS "s" (lamS "a" (caseS (varS "s") [(conP "Show" [varP "f"], appS [varS "f", varS "a"])])), appS [varS "Show", lamS "x" (ifS (varS "x") (litString "True") (litString "False"))], litBool False]

testTypeInterface :: SpecWith ()
testTypeInterface = do
    testHasType "test000" (test000, tString)
    testEvalsTo "test000" (test000, Value (String "hello"))
    testHasType "test010" (test010, tString)
    testEvalsTo "test010" (test010, Value (String "False"))

testEvalsTo :: Text -> (Expr, Value Eval) -> SpecWith ()
testEvalsTo name (expr, val) =
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
    [ ("Show" , dataCon "Show" 1)
    , ("id"   , evalE (lamS "x" (varS "x")))
    ]

runEvalTest :: Expr -> Either EvalError (Value Eval)
runEvalTest = evalExpr testEnv

testHasType :: Name -> (Expr, Type) -> SpecWith ()
testHasType name (expr, ty) =
    describe description (it describeSuccess test)
  where
    description = unpack $
        name <> ": " <> Pretty.expr expr

    describeSuccess = unpack $
        "✔ has type : " <> Pretty._type ty

    describeFailure = unpack $
        "Expected type to be identical to : "
            <> Pretty._type ty
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
    [ ("Show" , Forall ["a"] (TArr (TArr (TVar "a") tString) (TApp (TCon "Show") (TVar "a"))))
    , ("id"   , Forall ["a"] (TArr (TVar "a") (TVar "a")))
    ])
