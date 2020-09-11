{-# LANGUAGE OverloadedStrings #-}
module Tau.TypeUnificationTests where

import Data.Either
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
        (arrT (varT "a") (varT "b"))
        (arrT tInt tInt)

    failUnifyTypes
        (arrT (varT "a") (varT "a"))
        (arrT tInt tBool)

    succeedUnifyTypes
        (arrT (varT "a") (varT "a"))
        (arrT tInt tInt)

    succeedUnifyTypes
        (arrT (varT "a") (arrT (varT "b") (varT "a")))
        (arrT (varT "a") (arrT tInt (varT "a")))

    succeedUnifyTypes
        (arrT (varT "a") (arrT (varT "b") (varT "a")))
        (arrT (varT "a") (arrT tInt (varT "b")))

    failUnifyTypes
        (arrT (varT "a") (arrT (varT "b") (varT "a")))
        (arrT tInt (arrT tInt tBool))

    succeedUnifyTypes
        (appT (conT "List") (varT "a"))
        (appT (conT "List") tInt)

    failUnifyTypes
        (appT (conT "List") (varT "a"))
        tInt
