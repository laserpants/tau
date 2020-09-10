{-# LANGUAGE OverloadedStrings #-}
import Data.Either
import Test.Hspec
import Tau.Type

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe "The types t1 and t2" $

        it "✗ fails to unify" $
            isLeft result

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = unify t1 t2
    describe "The types t1 and t2" $ do

        it "✔ yields a substitution" $
            isRight result

        it "✔ that unifies the types" $ do
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
