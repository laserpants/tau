{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.SubstitutionTests where

import Data.Map.Strict (Map)
import Data.Maybe (isNothing)
import Data.Text (pack)
import Tau.Compiler.Substitute
import Tau.Pretty
import Tau.Util
import Tau.Type
import Test.Hspec hiding (describe, it)
import TestUtils
import qualified Tau.Compiler.Substitute as Sub

--testSubstitution :: SpecWith ()
--testSubstitution = 
--    pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

applyTo :: Substitution Type -> Type -> Type -> SpecWith ()
applyTo sub ty res =
    describe ("apply " <> prettyPrint (show sub) <> " to " <> prettyPrint ty) $ do
        it ("✔ returns: " <> prettyPrint res)
            (apply sub ty == res)

testApply :: SpecWith ()
testApply = do 

    applyTo 
        (mapsTo "a" tInt) 
        _a
        tInt

    applyTo 
        (mapsTo "a" tInt) 
        (_a `tArr` _b)
        (tInt `tArr` _b)

    applyTo 
        (mapsTo "a" tInt) 
        (_a `tArr` _a)
        (tInt `tArr` tInt)

    applyTo 
        (mapsTo "a" tInt) 
        tInt
        tInt

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--composeAndApplyTo :: TypeSubstitution -> TypeSubstitution -> Type -> Type -> SpecWith ()
--composeAndApplyTo sub1 sub2 ty res =
--    describe ("apply TODO to " <> prettyPrint ty) $ do
--        it ("✔ returns: " <> prettyPrint res)
--            (apply (compose sub1 sub2) ty == res)
--
--testCompose ::  SpecWith ()
--testCompose = do 
--
--    composeAndApplyTo
--        (fromList [ ("a", tInt) ]) 
--        (fromList [ ("b", tBool) ])
--        _a
--        tInt
--
--    composeAndApplyTo
--        (fromList [ ("a", tInt) ]) 
--        (fromList [ ("b", tBool) ])
--        _b
--        tBool
--
--    composeAndApplyTo
--        (fromList [ ("b", tBool) ])
--        (fromList [ ("a", tInt) ]) 
--        _a
--        tInt
--
--    composeAndApplyTo
--        (fromList [ ("b", tBool) ])
--        (fromList [ ("a", tInt) ]) 
--        _b
--        tBool
--
--    composeAndApplyTo
--        (fromList [ ("b", tBool) ])
--        (fromList [ ("a", tInt) ]) 
--        (_a `tArr` _b)
--        (tInt `tArr` tBool)
--
--    composeAndApplyTo
--        (fromList [ ("b", tBool) ])
--        (fromList [ ("a", tVar kTyp "b") ]) 
--        _a
--        tBool
--
--    composeAndApplyTo
--        (fromList [ ("b", tBool) ])
--        (fromList [ ("a", tVar kTyp "b") ]) 
--        _b
--        tBool
--
--    composeAndApplyTo
--        (compose (fromList [ ("a3", tVar kTyp "a4") ]) (fromList [ ("a2", tVar kTyp "a3") ]))
--        (fromList [ ("a1", tVar kTyp "a2") ]) 
--        (tVar kTyp "a1")
--        (tVar kTyp "a4")
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testMerge ::  SpecWith ()
--testMerge = do 
--
--    describe "TODO" $ do
--        it "✗ fails"
--            (isNothing (merge (Sub.fromList [("a", tInt), ("b", tInt)]) (Sub.fromList [("b", tBool)]) :: Maybe TypeSubstitution))
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testFromList ::  SpecWith ()
--testFromList = do 
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testToList ::  SpecWith ()
--testToList = do 
--
--    describe "TODO" $ do
--        pure ()
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--testNull ::  SpecWith ()
--testNull = do 
--
--    describe "The null substitution" $ do
--        it "✔ is an empty map"
--            (getSub Sub.null == (mempty :: Map Name Type))
