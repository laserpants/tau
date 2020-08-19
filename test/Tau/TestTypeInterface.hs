{-# LANGUAGE OverloadedStrings #-}
module Tau.TestTypeInterface where

import Tau.Ast
import Tau.Core
import Tau.Type
import Test.Hspec

-- show 123
test000 :: Expr
test000 = appS [varS "show", litInt 123]

-- show False
test010 :: Expr
test010 = appS [varS "show", litBool False]

testTypeInterface :: SpecWith ()
testTypeInterface = pure ()
