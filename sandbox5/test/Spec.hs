{-# LANGUAGE OverloadedStrings #-}
import Tau.Compiler.SubstitutionTests
import Tau.Compiler.TranslationTests
import Tau.Compiler.TypecheckTests
import Tau.Compiler.UnificationTests
import Tau.PrettyTests
import Tau.TypeTests
import Test.Hspec hiding (describe, it)
import Utils

main :: IO ()
main =
    hspec $ do
        describe "Tau.Type.kindOf"                         testKindOf
        describe "Tau.Type.typeVars"                       testTypeVars
        describe "Tau.Type.upgrade"                        testUpgrade
        describe "Tau.Type.tupleCon"                       testTupleCon

        describe "Tau.Compiler.Unification.bind"           testBind
        describe "Tau.Compiler.Unification.isRow"          testIsRow
        describe "Tau.Compiler.Unification.unify"          testUnify
        describe "Tau.Compiler.Unification.match"          testMatch
        describe "Tau.Compiler.Unification.unifyPairs"     testUnifyPairs
        describe "Tau.Compiler.Unification.matchPairs"     testMatchPairs
        describe "Tau.Compiler.Unification.unifyRowTypes"  testUnifyRowTypes
        describe "Tau.Compiler.Unification.matchRowTypes"  testMatchRowTypes
        describe "Tau.Compiler.Unification.unfoldRow"      testTypeToRow

        describe "Tau.Compiler.Substitution"               testSubstitution
        describe "Tau.Compiler.Substitution.apply"         testApply
        describe "Tau.Compiler.Substitution.compose"       testCompose
        describe "Tau.Compiler.Substitution.merge"         testMerge
        describe "Tau.Compiler.Substitution.fromList"      testFromList
        describe "Tau.Compiler.Substitution.toList"        testToList
        describe "Tau.Compiler.Substitution.null"          testNull

        describe "Tau.Compiler.Typecheck.inferPattern"     testInferPattern

        describe "Tau.Compiler.Tranlsation.simplifyExpr"   testSimplifyExpr

        describe "Tau.Compiler.Substitution.null"          testNull
        describe "Tau.Pretty (Prim)"                       testPrettyPrim
        describe "Tau.Pretty (Type)"                       testPrettyType
        describe "Tau.Pretty (Kind)"                       testPrettyKind
        describe "Tau.Pretty (Pattern)"                    testPrettyPattern
        describe "Tau.Pretty (Predicates)"                 testPrettyPredicates
