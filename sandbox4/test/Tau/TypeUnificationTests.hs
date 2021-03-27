{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeUnificationTests where

import Data.Either (isLeft, isRight)
import Tau.Comp.Type.Substitution
import Tau.Comp.Type.Unification
import Tau.Lang.Type
import Tau.Lang.Type.Row
import Test.Hspec
import Utils

testDescription :: Type -> Type -> String
testDescription t1 t2 =
    "The types " <> prettyParString t1 <> " and " <> prettyParString t2 

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
                toRowRep = rowRepresentation . unfoldRow
            if Just kRow == kindOf r1
                then toRowRep r1 == toRowRep r2
                else r1 == r2

testTypeUnification :: SpecWith ()
testTypeUnification = do

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

    describe "\nRow types\n" $ do

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
--          { name : String, id : Int, shoeSize : Float }
            (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))
--          { shoeSize : Float, id : Int | r }
            (tRowExtend "shoeSize" tFloat (tRowExtend "id" tInt (tVar kRow "r")))

        succeedUnifyTypes
            (tRowExtend "name" tString (tRowExtend "id" tInt (tRowExtend "shoeSize" tFloat tEmptyRow)))
            (tRowExtend "name" tString (tRowExtend "id" tInt (tVar kRow "r")))
