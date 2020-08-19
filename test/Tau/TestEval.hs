{-# LANGUAGE OverloadedStrings #-}
module Tau.TestEval where

import Control.Monad.Reader
import Data.Text (Text, pack, unpack)
import Data.Either (fromRight)
import Tau.Ast
import Tau.Core
import Tau.Eval
import Tau.Pattern
import Tau.Prim
import Tau.Value
import Test.Hspec
import Utils
import qualified Data.Map.Strict as Map
import qualified Utils.Pretty as Pretty

-- \a -> \b -> a
test000 :: Expr
test000 = lamS "a" (lamS "b" (varS "a"))

-- let const = \a -> \b -> a in const ()
-- <<function>>
test010 :: Expr
test010 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit])

-- let const = \a -> \b -> a in const () 5  
-- ()
test020 :: Expr
test020 = letS "const" (lamS "a" (lamS "b" (varS "a"))) (appS [varS "const", litUnit, litInt 5])

-- (\xs -> case xs of { Cons y ys -> 1; Nil -> 2 }) (Cons 5 Nil)
-- 1
test030 :: Expr
test030 = appS [lamS "xs" (caseS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Cons", litInt 5, appS [varS "Nil"]]]

-- (\xs -> case xs of { Cons y ys -> 1; Nil -> 2 }) Nil
-- 2
test040 :: Expr
test040 = appS [lamS "xs" (caseS (varS "xs") [(conP "Cons" [varP "y", varP "ys"], litInt 1), (conP "Nil" [], litInt 2)]), appS [varS "Nil"]]

-- let plus = \a -> \b -> a + b in let plus5 = plus 5 in let id = \x -> x in (id plus5) (id 3)
-- 8
test050 :: Expr
test050 = letS "plus" (lamS "a" (lamS "b" (addS (varS "a") (varS "b")))) (letS "plus5" (appS [varS "plus", litInt 5]) (letS "id" (lamS "x" (varS "x")) (appS [appS [varS "id", varS "plus5"], appS [varS "id", litInt 3]])))

-- let id = \x -> x in let x = (id, 4) in (fst x) (snd x) + 1
-- 5
test060 :: Expr
test060 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (addS (appS [varS "fst", varS "x", varS "snd", varS "x"]) (litInt 1)))

-- let id = \x -> x in let x = (id, 4) in (fst x)
-- <<function>>
test070 :: Expr
test070 = letS "id" (lamS "x" (varS "x")) (letS "x" (appS [varS "Tuple2", varS "id", litInt 4]) (appS [varS "fst", varS "x"]))

test080 :: Expr
test080 = letS "x" (varS "x") (varS "x")

testEval :: SpecWith ()
testEval = do
    testIsFunction test000               "test000"
    testIsFunction test010               "test010"
    testEvalsTo (test020, Value Unit)    "test020"
    testEvalsTo (test030, Value (Int 1)) "test030"
    testEvalsTo (test040, Value (Int 2)) "test040"
    testEvalsTo (test050, Value (Int 8)) "test050"
    testEvalsTo (test060, Value (Int 5)) "test060"
    testIsFunction test070               "test070"
    testFailsWithError (test080, UnboundVariable "x") "test080"

testFailsWithError :: (Expr, EvalError) -> Name -> SpecWith ()
testFailsWithError (expr, err) name =
    describe description (it describeSuccess test)
  where
    description = unpack $ name <> ": " <> Pretty.expr expr

    describeSuccess = unpack "✗ fails with error " <> show err

    test = case runTest expr of
        Left err' | err' == err ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right{} ->
            expectationFailure ("Expected evaluation to fail with " <> show err)

testIsFunction :: Expr -> Text -> SpecWith ()
testIsFunction expr name = 
    describe description (it describeSuccess test)
  where
    description = unpack $ name <> ": " <> Pretty.expr expr

    describeSuccess = unpack "✔ is a function"

    test = case runTest expr of
        Right Closure{} ->
            pass

        Right result ->
            expectationFailure $ unpack ("Unexpected result: " <> Pretty.value result)

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

testEvalsTo :: (Expr, Value Eval) -> Text -> SpecWith ()
testEvalsTo (expr, val) name = 
    describe description (it describeSuccess test)
  where
    description = unpack $ name <> ": " <> Pretty.expr expr

    describeSuccess = unpack $ "✔ evaluates to " <> Pretty.value val

    test = case (runTest expr, val) of
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
    [ ("Cons"   , dataCon "Cons" 2)
    , ("Nil"    , dataCon "Nil" 0)
    , ("Tuple2" , dataCon "Tuple2" 2)
                  -- \p -> case p of Tuple2 a b => a
    , ("fst"    , evalE (lamS "p" (caseS (varS "p") [(conP "Tuple2" [varP "a", varP "b"], varS "a")])))
                  -- \p -> case p of Tuple2 a b => b
    , ("snd"    , evalE (lamS "p" (caseS (varS "p") [(conP "Tuple2" [varP "a", varP "b"], varS "b")])))
    ]

runTest :: Expr -> Either EvalError (Value Eval)
runTest = evalExpr testEnv
