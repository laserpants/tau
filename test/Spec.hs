import Tau.TestInfer
import Tau.TestPatternCheck
import Tau.TestUnify
import Tau.TestSubstitute
import Test.Hspec

main :: IO ()
main =
    hspec $ do
--        describe "Eval" testEval
        describe "Unify" testUnify
        describe "Infer" testInfer
        describe "PatternCheck" testPatternCheck
        describe "Substitute" testSubstitute
