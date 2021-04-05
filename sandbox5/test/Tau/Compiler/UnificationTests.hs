{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.UnificationTests where

import Data.Either (isLeft, isRight)
import Data.Text (Text)
import Tau.Compiler.Substitution
import Tau.Compiler.Unification
import Tau.Lang
import Tau.Pretty
import Tau.Row
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

    describe "TODO" $ do pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testDescription :: Type -> Type -> Text
testDescription t1 t2 = "The types " <> prettyText t1 <> " and " <> prettyText t2 

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe (testDescription t1 t2) $
        it "✗ fails to unify" $
            isLeft result

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe (testDescription t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types" $ do
            let Right sub = result
                r1 = apply sub t1 
                r2 = apply sub t2
            if kRow == kindOf r1
                then typeToRow r1 == typeToRow r2
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

    failUnifyTypes
        (tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow))
        (tRowExtend "id" tString (tRowExtend "name" tInt tEmptyRow))

    succeedUnifyTypes
        (tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow))
        (tRowExtend "id" tInt (tRowExtend "name" tString tEmptyRow))

    succeedUnifyTypes
        (tRowExtend "x" tInt (tVar kRow "r"))
        (tRowExtend "x" tInt (tVar kRow "r"))

    failUnifyTypes
        (tRowExtend "x" tInt (tVar kRow "r"))
        (tRowExtend "y" tInt (tVar kRow "r"))

    succeedUnifyTypes
        (tRowExtend "x" tInt (tVar kRow "r"))
        (tRowExtend "x" tInt (tVar kRow "s"))

    succeedUnifyTypes
        (tRowExtend "id" tInt (tVar kRow "r"))
        (tRowExtend "id" tInt (tRowExtend "name" tString tEmptyRow))

    succeedUnifyTypes
        (tRowExtend "id" tInt (tRowExtend "name" tString tEmptyRow))
        (tRowExtend "id" tInt (tVar kRow "r"))

    succeedUnifyTypes
        (tRowExtend "id" tInt (tRowExtend "password" tString (tRowExtend "name" tString tEmptyRow)))
        (tRowExtend "id" tInt (tVar kRow "r"))

    succeedUnifyTypes
        (tRowExtend "id" tInt (tRowExtend "password" tString (tRowExtend "name" tString tEmptyRow)))
        (tVar kRow "r")

    failUnifyTypes
        (tRowExtend "id" tInt (tRowExtend "password" tString (tRowExtend "name" tString tEmptyRow)))
        (tVar kTyp "r")  --- Note: Not a row kind!

    succeedUnifyTypes
        (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))
        (tRowExtend "shoeSize" tFloat (tRowExtend "id" tInt (tRowExtend "name" tString tEmptyRow)))

    succeedUnifyTypes
        -- { name : String, shoeSize : Float }
        (tRowExtend "name" tString (tRowExtend "shoeSize" tFloat tEmptyRow))
        -- { shoeSize : Float | r }
        (tRowExtend "shoeSize" tFloat (tVar kRow "r"))

    succeedUnifyTypes
        -- { name : String, id : Int, shoeSize : Float }
        (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))
        -- { shoeSize : Float, id : Int | r }
        (tRowExtend "shoeSize" tFloat (tRowExtend "id" tInt (tVar kRow "r")))

    succeedUnifyTypes
        -- { name : String, id : Int, shoeSize : Float }
        (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))
        -- { shoeSize : Float | r }
        (tRowExtend "shoeSize" tFloat (tVar kRow "r"))

    succeedUnifyTypes
        (tRowExtend "shoeSize" tFloat (tVar kRow "r"))
        (tRowExtend "name" tString (tRowExtend "shoeSize" tFloat tEmptyRow))

    succeedUnifyTypes
        (tRowExtend "shoeSize" tFloat (tRowExtend "id" tInt (tVar kRow "r")))
        (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))

    succeedUnifyTypes
        (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))
        (tRowExtend "name" tString (tRowExtend "id" tInt (tVar kRow "r")))

    succeedUnifyTypes
        (tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow))
        (tRowExtend "name" tString (tRowExtend "id" (tVar kTyp "a") tEmptyRow))

    succeedUnifyTypes
        (tRowExtend "name" tString (tRowExtend "id" (tVar kTyp "a") tEmptyRow))
        (tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testMatchRowTypes :: SpecWith ()
testMatchRowTypes = do

    describe "TODO" $ do
        pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

succeedTypeToRow :: Type -> Row Type -> SpecWith ()
succeedTypeToRow ty row =
    describe ("The type " <> prettyText ty) $ 
        it ("✔ unfolds to " <> prettyText row)
            (typeToRow ty == row)

testTypeToRow :: SpecWith ()
testTypeToRow = do

    succeedTypeToRow 
        (tVar kRow "r") 
        (rVar "r")

    succeedTypeToRow 
        tEmptyRow
        rNil

    succeedTypeToRow 
        (tRowExtend "id" tInt tEmptyRow)
        (rExt "id" tInt rNil)

    succeedTypeToRow 
        (tRowExtend "id" tInt (tVar kRow "r"))
        (rExt "id" tInt (rVar "r"))

    succeedTypeToRow 
        (tRowExtend "name" tString (tRowExtend "id" tInt (tVar kRow "r")))
        (rExt "name" tString (rExt "id" tInt (rVar "r")))

    succeedTypeToRow 
        (tRowExtend "name" tString (tRowExtend "id" tInt tEmptyRow))
        (rExt "name" tString (rExt "id" tInt rNil))
