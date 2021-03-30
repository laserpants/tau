{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeTests where

import Tau.Type
import Test.Hspec
import Utils

testTypes :: SpecWith ()
testTypes = do
    pure ()

testKindOf :: SpecWith ()
testKindOf = do

    describeTest "The kind of Bool" $ do
        it "✔ is *" 
            (kindOf tBool == kTyp)

    describeTest "The kind of (Int -> Int)" $ do
        it "✔ is *" 
            (kindOf (tInt `tArr` tInt) == kTyp)

    describeTest "The kind of (List a)" $ do
        it "✔ is *" 
            (kindOf (tList (tVar kTyp "a")) == kTyp)

    describeTest "The kind of (List Int)" $ do
        it "✔ is *" 
            (kindOf (tList tInt) == kTyp)

    describeTest "The kind of List" $ do
        it "✔ is * -> *" 
            (kindOf tListCon == kFun)
