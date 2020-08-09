import Tau.TestInfer
import Tau.TestUnify
import Test.Hspec

main :: IO ()
main =
    hspec $ do
--        describe "Eval" testEval
        describe "Unify" testUnify
        describe "Infer" testInfer
