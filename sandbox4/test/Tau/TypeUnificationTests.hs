{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeUnificationTests where

import Data.Either (isLeft, isRight)
import Tau.Comp.Type.Substitution
import Tau.Comp.Type.Unification
import Tau.Lang.Type
import Test.Hspec
import Utils

testDescription :: Type -> Type -> String
testDescription t1 t2 =
    "The types " <> prettyParString t1 <> " and " <> prettyParString t2 

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
            apply sub t1 == apply sub t2

testTypeUnification :: SpecWith ()
testTypeUnification = do
    succeedUnifyTypes
        (_a `tArr` _b)
        (tInt `tArr` tInt)

--        $(parseType "a -> b")
--        $(parseType "Int -> Int")

    failUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tBool)

--        $(parseType "a -> a")
--        $(parseType "Int -> Bool")

    succeedUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tInt)

--        $(parseType "a -> a")
--        $(parseType "Int -> Int")

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _a)

--        $(parseType "a -> b -> a")
--        $(parseType "a -> Int -> a")

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _b)

--        $(parseType "a -> b -> a")
--        $(parseType "a -> Int -> b")

    failUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (tInt `tArr` tInt `tArr` tBool)

--        $(parseType "a -> b -> a")
--        $(parseType "Int -> Int -> Bool")

    succeedUnifyTypes
        (tList _a)
        (tList tInt)
        
--        $(parseType "List a")
--        $(parseType "List Int")

    failUnifyTypes
        (tList _a)
        tInt

--        $(parseType "List a")
--        tInt

    succeedUnifyTypes
        tInt
        tInt

    failUnifyTypes
        tUnit
        tInt
