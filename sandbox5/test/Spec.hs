import Tau.Compiler.SubstitutionTests
import Tau.Compiler.UnificationTests
import Tau.TypeTests
import Test.Hspec hiding (describe, it)
import Utils

main :: IO ()
main =
    hspec $ do
        describe "Tau.Type.kindOf"                   testKindOf
        describe "Tau.Type.typeVars"                 testTypeVars
        describe "Tau.Type.upgrade"                  testUpgrade

        describe "Tau.Compiler.Unification.bind"     testBind
        describe "Tau.Compiler.Unification.isRow"    testIsRow

        describe "Tau.Compiler.Substitution"         testSubstitution
        describe "Tau.Compiler.Substitution.apply"   testApply
        describe "Tau.Compiler.Substitution.compose" testCompose
        describe "Tau.Compiler.Substitution.merge"   testMerge
