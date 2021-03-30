module Tau.Compiler.SubstitutionTests where

import Data.Text (pack)
import Tau.Compiler.Substitution
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils

testSubstitution :: SpecWith ()
testSubstitution = 
    pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

applyTo :: TypeSubstitution -> Type -> Type -> SpecWith ()
applyTo sub ty res =
    describe "apply TODO to TODO" $ do
        it "✔ returns TODO"
            (apply sub ty == res)

testApply :: SpecWith ()
testApply = do 

    applyTo 
        (mapsTo "a" tInt) 
        (tVar kTyp "a") 
        tInt

    applyTo 
        (mapsTo "a" tInt) 
        (tVar kTyp "a" `tArr` tVar kTyp "b")
        (tInt `tArr` tVar kTyp "b")

    applyTo 
        (mapsTo "a" tInt) 
        (tVar kTyp "a" `tArr` tVar kTyp "a")
        (tInt `tArr` tInt)

    applyTo 
        (mapsTo "a" tInt) 
        tInt
        tInt

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testCompose ::  SpecWith ()
testCompose = do 
    pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testMerge ::  SpecWith ()
testMerge = do 
    pure ()
