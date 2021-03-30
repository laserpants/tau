{-# LANGUAGE OverloadedStrings #-}
import Tau.Compiler.SubstitutionTests
import Tau.Compiler.UnificationTests
import Tau.TypeTests
import Test.Hspec hiding (describe, it)
import Utils

main :: IO ()
main =
    hspec $ do
        describe "Tau.Type.kindOf"                        testKindOf
        describe "Tau.Type.typeVars"                      testTypeVars
        describe "Tau.Type.upgrade"                       testUpgrade

        describe "Tau.Compiler.Unification.bind"           testBind
        describe "Tau.Compiler.Unification.isRow"          testIsRow
        describe "Tau.Compiler.Unification.unify"          testUnify
        describe "Tau.Compiler.Unification.match"          testMatch
        describe "Tau.Compiler.Unification.unifyPairs"     testUnifyPairs
        describe "Tau.Compiler.Unification.matchPairs"     testMatchPairs
        describe "Tau.Compiler.Unification.unifyRowTypes"  testUnifyRowTypes
        describe "Tau.Compiler.Unification.matchRowTypes"  testMatchRowTypes

        describe "Tau.Compiler.Substitution"               testSubstitution
        describe "Tau.Compiler.Substitution.apply"         testApply
        describe "Tau.Compiler.Substitution.compose"       testCompose
        describe "Tau.Compiler.Substitution.merge"         testMerge
        describe "Tau.Compiler.Substitution.fromList"      testFromList
        describe "Tau.Compiler.Substitution.toList"        testToList
