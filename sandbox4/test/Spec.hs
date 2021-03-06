import Test.Hspec
import Tau.CoreEvalTests
import Tau.PatternAnomaliesTests
import Tau.TypeInferenceTests
import Tau.TypeSubstitutionTests
import Tau.TypeUnificationTests

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nType inference\n" testTypeInference
        describe "\nType substitution\n" testTypeSubstitution
        describe "\nPattern anomalies\n" testPatternAnomalies
        describe "\nCore evaluation\n" testCoreEval
