{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.TypeUnificationTests where

import Data.Either
import Tau.Type
import Tau.Util.TH
import Test.Hspec
import Utils

description :: Type -> Type -> String
description t1 t2 =
    "The types (" <> prettyString t1
     <> ") and (" <> prettyString t2 <> ")"

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe (description t1 t2) $
        it "✗ fails to unify" $
            isLeft result

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe (description t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types" $ do
            let Right sub = result
            apply sub t1 == apply sub t2

testTypeUnification :: SpecWith ()
testTypeUnification = do
    succeedUnifyTypes
        $(parseType "a -> b")
        $(parseType "Int -> Int")

    failUnifyTypes
        $(parseType "a -> a")
        $(parseType "Int -> Bool")

    succeedUnifyTypes
        $(parseType "a -> a")
        $(parseType "Int -> Int")

    succeedUnifyTypes
        $(parseType "a -> b -> a")
        $(parseType "a -> Int -> a")

    succeedUnifyTypes
        $(parseType "a -> b -> a")
        $(parseType "a -> Int -> b")

    failUnifyTypes
        $(parseType "a -> b -> a")
        $(parseType "Int -> Int -> Bool")

    succeedUnifyTypes
        $(parseType "List a")
        $(parseType "List Int")

    failUnifyTypes
        $(parseType "List a")
        tInt
