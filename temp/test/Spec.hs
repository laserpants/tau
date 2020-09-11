import Tau.EvalTests
import Tau.ParserTests
import Tau.PatternAnomaliesCheckTests
import Tau.PatternCompilerTests
import Tau.SubstitutionTests
import Tau.TypeUnificationTests
import Test.Hspec

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nParser\n" testParser
        describe "\nPattern compiler\n" testPatternCompiler
        describe "\nPattern anomalies check\n" testPatternAnomaliesCheck
        describe "\nEval\n" testEval
        describe "\nSubstitutions\n" testSubstitute
