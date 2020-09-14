{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.TypeUnificationTests where

import Data.Either
import TH
import Tau.Type
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
        $(mkType "a -> b")
        $(mkType "Int -> Int")

    failUnifyTypes
        $(mkType "a -> a")
        $(mkType "Int -> Bool")

    succeedUnifyTypes
        $(mkType "a -> a")
        $(mkType "Int -> Int")

    succeedUnifyTypes
        $(mkType "a -> b -> a")
        $(mkType "a -> Int -> a")

    succeedUnifyTypes
        $(mkType "a -> b -> a")
        $(mkType "a -> Int -> b")

    failUnifyTypes
        $(mkType "a -> b -> a")
        $(mkType "Int -> Int -> Bool")

    succeedUnifyTypes
        $(mkType "List a")
        $(mkType "List Int")

    failUnifyTypes
        $(mkType "List a")
        tInt
