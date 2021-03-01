import Test.Hspec
import Tau.TypeUnificationTests
import Tau.TypeInferenceTests

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nType inference\n" testTypeInference
--        describe "\nType substitution\n" testSubstitute