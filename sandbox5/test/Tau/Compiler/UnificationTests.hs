{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.UnificationTests where

import Data.Either (isLeft, isRight)
import Data.Text (Text)
import Tau.Compiler.Substitution
import Tau.Compiler.Unification
import Tau.Lang
import Tau.Pretty
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils

testBind :: SpecWith ()
testBind = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testIsRow :: SpecWith ()
testIsRow = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testDescription :: Type -> Type -> Text
testDescription t1 t2 = "The types " <> prettyText t1 <> " and " <> prettyText t2 

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe (testDescription t1 t2) $
        it "✗ fails to unify\n" $
            isLeft result

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe (testDescription t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types\n" $ do
            let Right sub = result
                r1 = apply sub t1 
                r2 = apply sub t2
                toRowRep = undefined -- TODO rowRepresentation . unfoldRow
            if kRow == kindOf r1
                then undefined -- TODO toRowRep r1 == toRowRep r2
                else r1 == r2

testUnify :: SpecWith ()
testUnify = do

    succeedUnifyTypes
        (_a `tArr` _b)
        (tInt `tArr` tInt)

    failUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tBool)

    succeedUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tInt)

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _a)

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _b)

    failUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (tInt `tArr` tInt `tArr` tBool)

    succeedUnifyTypes
        (tList _a)
        (tList tInt)
        
    succeedUnifyTypes
        (tList _a)
        (tList _b)

    failUnifyTypes
        (tList _a)
        (tPair _a _b)

    succeedUnifyTypes
        (tPair _a _a)
        (tPair _a _b)

    failUnifyTypes
        (tPair _a _a)
        (tPair tInt tBool)

    failUnifyTypes
        (tList _a)
        tInt

    succeedUnifyTypes
        tInt
        tInt

    failUnifyTypes
        tUnit
        tInt

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testMatch :: SpecWith ()
testMatch = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testUnifyPairs :: SpecWith ()
testUnifyPairs = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testMatchPairs :: SpecWith ()
testMatchPairs = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testUnifyRowTypes :: SpecWith ()
testUnifyRowTypes = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testMatchRowTypes :: SpecWith ()
testMatchRowTypes = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

succeedUnfoldRow :: Type -> Row Type -> SpecWith ()
succeedUnfoldRow ty row =
    describe ("The type " <> prettyText ty) $ 
        it ("✔ unfolds to " <> prettyText row)
            (unfoldRowType ty == row)

testUnfoldRowType :: SpecWith ()
testUnfoldRowType = do

    succeedUnfoldRow 
        (tVar kRow "r") 
        (rVar "r")

    succeedUnfoldRow 
        tEmptyRow
        rNil

    succeedUnfoldRow 
        (tRowExtend "id" tInt tEmptyRow)
        (rExt "id" tInt rNil)

    succeedUnfoldRow 
        (tRowExtend "id" tInt (tVar kRow "r"))
        (rExt "id" tInt (rVar "r"))

    succeedUnfoldRow 
        (tRowExtend "name" tString (tRowExtend "id" tInt (tVar kRow "r")))
        (rExt "name" tString (rExt "id" tInt (rVar "r")))

    succeedUnfoldRow 
        (tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow))
        (rExt "name" tString (rExt "id" tInt rNil))
