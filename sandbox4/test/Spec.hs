import Tau.CoreEvalTests
import Tau.ParserTests
import Tau.PatternAnomaliesTests
import Tau.TypeInferenceTests
import Tau.TypeSubstitutionTests
import Tau.TypeUnificationTests
import Test.Hspec

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nType inference\n" testTypeInference
        describe "\nType substitution\n" testTypeSubstitution
        describe "\nPattern anomalies\n" testPatternAnomalies
        describe "\nCore evaluation\n" testCoreEval
        describe "\nParser\n" testParser
