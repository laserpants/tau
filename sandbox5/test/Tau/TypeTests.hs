{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeTests where

import Data.Text (Text)
import Tau.Tool
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Data.Text as Text

testKindOf :: SpecWith ()
testKindOf = do

    describe "The kind of Bool" $ do
        it "✔ is *" 
            (kindOf tBool == kTyp)

    describe "The kind of (Int -> Int)" $ do
        it "✔ is *" 
            (kindOf (tInt `tArr` tInt) == kTyp)

    describe "The kind of (List a)" $ do
        it "✔ is *" 
            (kindOf (tList (tVar kTyp "a")) == kTyp)

    describe "The kind of (List Int)" $ do
        it "✔ is *" 
            (kindOf (tList tInt) == kTyp)

    describe "The kind of List" $ do
        it "✔ is * -> *" 
            (kindOf tListCon == kFun)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

typeVarsAre :: TypeT a -> [(Name, Kind)] -> (Text, [Text]) -> SpecWith ()
typeVarsAre ty vars (v, vs) =
    describe ("The free type variables in " <> v) $
        it ("✔ are [" <> Text.intercalate ", " vs <> "]")
            (typeVars ty == vars)

testTypeVars :: SpecWith ()
testTypeVars = do

    typeVarsAre 
        (tVar kTyp "v") 
        [("v", kTyp)] 
        ("v", ["v : *"])

    typeVarsAre 
        (tVar kTyp "a" `tArr` tVar kTyp "b") 
        [("a", kTyp), ("b", kTyp)] 
        ("a -> b", ["a : *", "b : *"])

    typeVarsAre 
        (tList (tVar kTyp "a") `tArr` tVar kTyp "b") 
        [("a", kTyp), ("b", kTyp)] 
        ("List a -> b", ["a : *", "b : *"])

    typeVarsAre 
        tInt
        [] 
        ("Int", [])

    typeVarsAre 
        (tApp (tVar kFun "m") (tVar kTyp "a")) 
        [("m", kFun), ("a", kTyp)] 
        ("m a", ["m : * -> *", "a : *"])

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testUpgrade :: SpecWith ()
testUpgrade = do
    pure ()
