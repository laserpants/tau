import Tau.EvalTests
import Tau.KindInferenceTests
import Tau.ParserTests
import Tau.PatternAnomaliesCheckTests
import Tau.PatternCompilerTests
import Tau.SubstitutionTests
import Tau.TypeInferenceTests
import Tau.TypeUnificationTests
import Test.Hspec
import Utils

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nParser\n" testParser
        describe "\nPattern compiler\n" testPatternCompiler
        describe "\nPattern anomalies check\n" testPatternAnomaliesCheck
        describe "\nEval\n" testEval
        describe "\nSubstitutions\n" testSubstitute
        describe "\nType inference\n" testTypeInference
        describe "\nKind inference\n" testKindInference
