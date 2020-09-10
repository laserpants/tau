{-# LANGUAGE OverloadedStrings #-}
import Data.Either
import Data.Text (pack, unpack)
import Tau.Print
import Tau.Type
import Test.Hspec

prettyString :: (Pretty p) => p -> String
prettyString = unpack . prettyPrint

description :: Type -> Type -> String
description t1 t2 =
    "The types (" <> prettyString t1 <> ") and (" <> prettyString t2 <> ")"

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

        it "✔ and it unifies the types" $ do
            let Right sub = result
            apply sub t1 == apply sub t2

testTypeUnification :: SpecWith ()
testTypeUnification = do
    succeedUnifyTypes (arrT (varT "a") (varT "b")) (arrT tInt tInt)
    failUnifyTypes (arrT (varT "a") (varT "a")) (arrT tInt tBool)

main :: IO ()
main =
    hspec $ do
        describe "Type unification\n" testTypeUnification
        pure ()
