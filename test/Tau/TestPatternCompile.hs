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
        , (conP "Cons" [varP "x", conP "Cons" [litP (Int 3), varP "ys"]], litString "three")
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

testEnv :: Env Eval
testEnv = Map.fromList
    [ ("Cons", dataCon "Cons" 2)
    , ("Nil", dataCon "Nil" 0)
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

testPatternCompile :: SpecWith ()
testPatternCompile = do
    testSuccess test010 "test010"
    testSuccess test020 "test020"

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
