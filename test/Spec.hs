import Tau.TestUnify
import Tau.TestInfer
import Test.Hspec

main :: IO ()
main =
    hspec $ do
--        describe "Eval" testEval
--        describe "Infer" testInfer
        describe "Unify" testUnify
