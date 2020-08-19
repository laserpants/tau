import Tau.TestEval
import Tau.TestInfer
import Tau.TestPatternCheck
import Tau.TestPatternCompile
import Tau.TestSubstitute
import Tau.TestTypeInterface
import Tau.TestUnify
import Test.Hspec

main :: IO ()
main =
    hspec $ do
        describe "Eval" testEval
        describe "Unify" testUnify
        describe "Infer" testInfer
        describe "PatternCheck" testPatternCheck
        describe "PatternCompile" testPatternCompile
        describe "Substitute" testSubstitute
        describe "Type Interface" testTypeInterface
