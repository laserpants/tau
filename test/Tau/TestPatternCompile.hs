{-# LANGUAGE OverloadedStrings #-}
module Tau.TestPatternCompile where

import Control.Monad.Supply
import Data.Text (Text, unpack)
import Tau.Ast
import Tau.Core
import Tau.Eval
import Tau.Pattern
import Tau.Pattern.Compile
import Tau.Prim
import Tau.Value
import Test.Hspec
import Utils
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Utils.Pretty as Pretty

testExpr1 :: Expr
testExpr1 =
    lamS "xs" (caseS (varS "xs")
        -- Cons 5 Nil => "one"
        [ (conP "Cons" [litP (Int 5), conP "Nil" []], litString "one")
        -- Cons x (Cons 3 ys) => "two"
        , (conP "Cons" [varP "x", conP "Cons" [litP (Int 3), varP "ys"]], litString "two")
        -- Cons 2 ys => "three"
        , (conP "Cons" [litP (Int 2), varP "ys"], litString "three")
        -- Cons x Nil => "four"
        , (conP "Cons" [varP "x", conP "Nil" []], litString "four")
        -- Cons y (Cons z (Cons a as)) => "five"
        , (conP "Cons" [varP "y", conP "Cons" [varP "z", conP "Cons" [varP "a", varP "as"]]], litString "five")
        -- xs => "six"
        , (varP "xs", litString "six")
        ])

testExpr2 :: Expr
testExpr2 =
    lamS "xs" (caseS (varS "xs")
        -- Cons 5 Nil => #1
        [ (conP "Cons" [litP (Int 5), conP "Nil" []], litString "#1")
        -- Cons x (Cons x xs) => #2
        , (conP "Cons" [varP "x", conP "Cons" [varP "x", varP "xs"]], litString "#2")
        -- Cons y (Cons z Nil) => #3
        , (conP "Cons" [varP "y", conP "Cons" [varP "z", conP "Nil" []]], litString "#3")
        ])

testExpr3 :: Expr
testExpr3 =
    lamS "xs" (caseS (varS "xs")
        -- Just 1 => 1
        [ (conP "Just" [litP (Int 1)], litInt 1)
        -- Just 2 => 2
        , (conP "Just" [litP (Int 2)], litInt 2)
        -- Nothing -> 3
        , (conP "Nothing" [], litInt 3)
        ])

testEnv :: Env Eval
testEnv = Map.fromList
    [ ("Cons", dataCon "Cons" 2)
    , ("Nil", dataCon "Nil" 0)
    , ("Just", dataCon "Just" 1)
    , ("Nothing", dataCon "Nothing" 0)
    ]

test010 :: (Expr, Expr, Value Eval)
test010 =
    ( testExpr1
    -- Cons 5 Nil
    , appS [varS "Cons", litInt 5, appS [varS "Nil"]]
    , Value (String "one") )

test020 :: (Expr, Expr, Value Eval)
test020 =
    ( testExpr1
    -- Cons 5 (Cons 4 Nil)
    , appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]
    , Value (String "six") )

test030 :: (Expr, Expr, Value Eval)
test030 =
    ( testExpr1
    -- Cons 2 (Cons 4 Nil)
    , appS [varS "Cons", litInt 2, appS [varS "Cons", litInt 4, appS [varS "Nil"]]]
    , Value (String "three") )

test040 :: (Expr, Expr, Value Eval)
test040 =
    ( testExpr1
    -- Cons 2 Nil
    , appS [varS "Cons", litInt 2, appS [varS "Nil"]]
    , Value (String "three") )

test050 :: (Expr, Expr, Value Eval)
test050 =
    ( testExpr1
    -- Nil
    , appS [varS "Nil"]
    , Value (String "six") )

test060 :: (Expr, Expr, Value Eval)
test060 =
    ( testExpr1
    -- Cons 3 Nil
    , appS [varS "Cons", litInt 3, appS [varS "Nil"]]
    , Value (String "four") )

test070 :: (Expr, Expr, Value Eval)
test070 =
    ( testExpr1
    -- Cons 5 (Cons 4 (Cons 3 Nil))
    , appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 4, appS [varS "Cons", litInt 3, varS "Nil"]]]
    , Value (String "five") )

test080 :: (Expr, Expr, Value Eval)
test080 =
    ( testExpr2
    -- Cons 5 (Cons 3 Nil)
    , appS [varS "Cons", litInt 5, appS [varS "Cons", litInt 3, appS [varS "Nil"]]]
    , Value (String "#2") )

test090 :: (Expr, Expr, Value Eval)
test090 =
    ( testExpr3
    -- Just 4
    , appS [varS "Just", litInt 4]
    , Value (Int 1) )

test100 :: (Expr, Expr, Value Eval)
test100 =
    ( testExpr3
    -- Just 1
    , appS [varS "Just", litInt 1]
    , Value (Int 1) )

test110 :: (Expr, Expr, Value Eval)
test110 =
    ( testExpr3
    -- Nil
    , appS [varS "Nil"]
    , Value (Int 1) )

testPatternCompile :: SpecWith ()
testPatternCompile = do
    testSuccess test010 "test010"
    testSuccess test020 "test020"
    testSuccess test030 "test030"
    testSuccess test040 "test040"
    testSuccess test050 "test050"
    testSuccess test060 "test060"
    testSuccess test070 "test070"
    testSuccess test080 "test080"
    testFailure test090 "test090"
    testSuccess test100 "test100"
    testFailure test110 "test110"

testSuccess :: (Expr, Expr, Value Eval) -> Text -> SpecWith ()
testSuccess (expr1, expr2, expected) name =
    describe description (it describeSuccess test)
  where
    description = unpack
        ( name <> ": ("
               <> Text.take 30 (Pretty.expr expr1)
               <> "...) "
               <> Pretty.expr expr2 )

    describeSuccess =
        unpack ("✔ evaluates to " <> Pretty.value expected)

    test = case evalExpr testEnv (appS [compileAll expr1, expr2]) of
        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right result ->
            if expected == result
                then pass
                else expectationFailure $ unpack
                        ( "Expected: " <> Pretty.value expected <>
                             "\nGot: " <> Pretty.value result )

testFailure :: (Expr, Expr, Value Eval) -> Text -> SpecWith ()
testFailure (expr1, expr2, expected) name =
    describe description (it describeSuccess test)
  where
    description = unpack
        ( name <> ": ("
               <> Text.take 30 (Pretty.expr expr1)
               <> "...) "
               <> Pretty.expr expr2 )

    describeSuccess =
        unpack "✗ failed to evaluate with RuntimeError"

    test = case evalExpr testEnv (appS [compileAll expr1, expr2]) of
        Left RuntimeError ->
            pass

        Left err ->
            expectationFailure ("Unexpected error: " <> show err)

        Right{} ->
            expectationFailure "Expected evaluation to fail"
