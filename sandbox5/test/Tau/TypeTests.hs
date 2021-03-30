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
            (kindOf (tList _a) == kTyp)

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
        _a
        [("a", kTyp)] 
        ("a", ["a : *"])

    typeVarsAre 
        (_a `tArr` _b) 
        [("a", kTyp), ("b", kTyp)] 
        ("a -> b", ["a : *", "b : *"])

    typeVarsAre 
        (tList _a `tArr` _b) 
        [("a", kTyp), ("b", kTyp)] 
        ("List a -> b", ["a : *", "b : *"])

    typeVarsAre 
        tInt
        [] 
        ("Int", [])

    typeVarsAre 
        (tApp (tVar kFun "m") _a) 
        [("m", kFun), ("a", kTyp)] 
        ("m a", ["m : * -> *", "a : *"])

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testUpgrade :: SpecWith ()
testUpgrade = do

    describe "Upgrading a type variable" $ do
        it "✔ returns the same type" 
            (upgrade _a == (tVar kTyp "a" :: PolyType))

    describe "Upgrading a type constructor" $ do
        it "✔ returns the same type" 
            (upgrade tInt == (tInt :: PolyType))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testTupleCon :: SpecWith ()
testTupleCon = do

    describe "The 2-tuple constructor" $ do
        it "✔ is (,)" 
            (tupleCon 2 == "(,)")

    describe "The 3-tuple constructor" $ do
        it "✔ is (,,)" 
            (tupleCon 3 == "(,,)")

    describe "The 4-tuple constructor" $ do
        it "✔ is (,,,)" 
            (tupleCon 4 == "(,,,)")
