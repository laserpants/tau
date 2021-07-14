{-# LANGUAGE OverloadedStrings #-}
import Tau.Compiler.PatternsTests
import Tau.Compiler.SubstitutionTests
import Tau.Compiler.TranslationTests
import Tau.Compiler.TranslationTests
import Tau.Compiler.TypecheckTests
import Tau.Compiler.UnificationTests
import Tau.ParserTests
import Tau.PrettyTests
import Tau.TypeTests
import Test.Hspec hiding (describe, it)
import TestUtils

main :: IO ()
main =
    hspec $ do
        describe "Tau.Type.kindOf"                         testKindOf
        describe "Tau.Type.typeVars"                       testTypeVars
        describe "Tau.Type.upgrade"                        testUpgrade
        describe "Tau.Type.tupleCon"                       testTupleCon

        describe "Tau.Compiler.Patterns"                   testPatterns

--        describe "Tau.Compiler.Unification.bind"           testBind
--        describe "Tau.Compiler.Unification.isRow"          testIsRow
        describe "Tau.Compiler.Unification.unify"          testUnify
        describe "Tau.Compiler.Unification.unifyRowTypes"  testUnifyRowTypes
--        describe "Tau.Compiler.Unification.match"          testMatch
--        describe "Tau.Compiler.Unification.unifyPairs"     testUnifyPairs
--        describe "Tau.Compiler.Unification.matchPairs"     testMatchPairs
--        describe "Tau.Compiler.Unification.matchRowTypes"  testMatchRowTypes
--        describe "Tau.Compiler.Unification.unfoldRow"      testTypeToRow
--
--        describe "Tau.Compiler.Substitution"               testSubstitution
        describe "Tau.Compiler.Substitution.apply"         testApply
--        describe "Tau.Compiler.Substitution.compose"       testCompose
--        describe "Tau.Compiler.Substitution.merge"         testMerge
--        describe "Tau.Compiler.Substitution.fromList"      testFromList
--        describe "Tau.Compiler.Substitution.toList"        testToList
--        describe "Tau.Compiler.Substitution.null"          testNull
--
--        describe "Tau.Compiler.Typecheck.inferPattern"     testInferPattern

        describe "Tau.Compiler.Typecheck.inferExprType"     testInferExprType
        describe "Tau.Compiler.Typecheck.inferRecordExpr"   testInferRecordExpr
        describe "Tau.Compiler.Typecheck.inferPatternType"  testInferPatternType

--        describe "Tau.Compiler.Tranlsation.simplifyExpr"   testSimplifyExpr
--
--        describe "Tau.Compiler.Substitution.null"          testNull
        describe "Tau.Pretty (Prim)"                       testPrettyPrim
        describe "Tau.Pretty (Type)"                       testPrettyType
        describe "Tau.Pretty (Kind)"                       testPrettyKind
--        describe "Tau.Pretty (Pattern)"                    testPrettyPattern
        describe "Tau.Pretty (Predicate)"                  testPrettyPredicates
        describe "Tau.Pretty (Expr)"                       testPrettyExpr

        describe "Tau.Parser (exprParser)"                 testExprParser
        describe "Tau.Parser (annExprParser)"              testAnnExprParser
        describe "Tau.Parser (match)"                      testExprParserMatch
        describe "Tau.Parser (patternParser)"              testPatternParser
        describe "Tau.Parser (annPatternParser)"           testAnnPatternParser
        describe "Tau.Parser (type)"                       testTypeParser
        describe "Tau.Parser (datatype)"                   testDatatypeParser

        describe "Bundle"                                  testCompileBundle
