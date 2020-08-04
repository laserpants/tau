{-# LANGUAGE OverloadedStrings #-}
module Tau.TestInfer where

import Data.Functor.Foldable
import Tau.Ast
import Tau.Type
import Tau.Type.Infer
import Tau.Type.Infer.Monad
import Tau.Prim
import Test.Hspec
import qualified Data.Map.Strict as Map

test010 :: Expr
test010 = Fix $ LetS [("const", Fix $ LamS "a" (Fix $ LamS "b" (Fix $ VarS "a")))] (Fix $ AppS [Fix $ VarS "const", Fix $ LitS Unit])

test012 :: Expr
test012 = Fix $ LamS "a" (Fix $ LamS "b" (Fix $ VarS "a"))

test014 :: Expr
test014 = Fix $ LamS "a" (Fix $ VarS "a")

testInfer :: SpecWith ()
testInfer = do
    undefined
