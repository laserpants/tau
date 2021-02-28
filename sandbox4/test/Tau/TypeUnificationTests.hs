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
    "The types (" <> prettyString t1 <> ") and (" <> prettyString t2 <> ")"

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
        (tVar kTyp "a" `tArr` tVar kTyp "b")
        (tInt `tArr` tInt)

--        $(parseType "a -> b")
--        $(parseType "Int -> Int")

    failUnifyTypes
        (tVar kTyp "a" `tArr` tVar kTyp "a")
        (tInt `tArr` tBool)

--        $(parseType "a -> a")
--        $(parseType "Int -> Bool")

    succeedUnifyTypes
        (tVar kTyp "a" `tArr` tVar kTyp "a")
        (tInt `tArr` tInt)

--        $(parseType "a -> a")
--        $(parseType "Int -> Int")

    succeedUnifyTypes
        (tVar kTyp "a" `tArr` tVar kTyp "b" `tArr` tVar kTyp "a")
        (tVar kTyp "a" `tArr` tInt `tArr` tVar kTyp "a")

--        $(parseType "a -> b -> a")
--        $(parseType "a -> Int -> a")

    succeedUnifyTypes
        (tVar kTyp "a" `tArr` tVar kTyp "b" `tArr` tVar kTyp "a")
        (tVar kTyp "a" `tArr` tInt `tArr` tVar kTyp "b")

--        $(parseType "a -> b -> a")
--        $(parseType "a -> Int -> b")

    failUnifyTypes
        (tVar kTyp "a" `tArr` tVar kTyp "b" `tArr` tVar kTyp "a")
        (tInt `tArr` tInt `tArr` tBool)

--        $(parseType "a -> b -> a")
--        $(parseType "Int -> Int -> Bool")

    succeedUnifyTypes
        (tList (tVar kTyp "a"))
        (tList tInt)
        
--        $(parseType "List a")
--        $(parseType "List Int")

    failUnifyTypes
        (tList (tVar kTyp "a"))
        tInt

--        $(parseType "List a")
--        tInt
