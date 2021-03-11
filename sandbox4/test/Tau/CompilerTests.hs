{-# LANGUAGE OverloadedStrings #-}
module Tau.CompilerTests where

-- (\[x, 2, 3] when x > 100 => x | _ => 8) [101,2,3] 

import Test.Hspec
import Utils

testCompiler :: SpecWith ()
testCompiler =
    pure ()
