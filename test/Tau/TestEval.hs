{-# LANGUAGE OverloadedStrings #-}
module Tau.TestEval where

import Control.Monad.Reader
import Data.Text (Text, pack, unpack)
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

testEval :: SpecWith ()
testEval = do
    testIsFunction test000               "test000"
    testIsFunction test010               "test010"
    testEvalsTo (test020, Value Unit)    "test020"
    testEvalsTo (test030, Value (Int 1)) "test030"
    testEvalsTo (test040, Value (Int 2)) "test040"

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

testEnv :: Env Eval
testEnv = Map.fromList
    [ ("Cons", dataCon "Cons" 2)
    , ("Nil", dataCon "Nil" 0)
    ]

runTest :: Expr -> Either EvalError (Value Eval)
runTest = evalExpr testEnv
