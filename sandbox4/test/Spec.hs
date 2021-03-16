import Tau.CompilerTests
import Tau.CoreEvalTests
import Tau.ParserTests
import Tau.PatternAnomaliesTests
import Tau.PatternCompilerTests
import Tau.PrettyPrinterTests
import Tau.ProgTranslTests
import Tau.SubstitutionTests
import Tau.TypeInferenceTests
import Tau.TypeSubstitutionTests
import Tau.TypeTests
import Tau.TypeUnificationTests
import Test.Hspec

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nType inference\n" testTypeInference
        describe "\nType substitution\n" testTypeSubstitution
        describe "\nPattern anomalies\n" testPatternAnomalies
        describe "\nPattern compiler\n" testPatternCompiler
        describe "\nCore evaluation\n" testCoreEval
        describe "\nParser\n" testParser
        describe "\nCompiler\n" testCompiler
        describe "\nPretty printer\n" testPrettyPrinter
        describe "\nTerm substitution\n" testTermSubtitution
        describe "\nTypes\n" testTypes
        describe "\nProgram translation\n" testProgTransl
