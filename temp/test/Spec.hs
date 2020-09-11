import Tau.TypeUnificationTests
import Tau.ParserTests
import Tau.PatternsCompilerTests
import Test.Hspec

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nParser\n" testParser
        describe "\nPatterns compiler\n" testPatternsCompiler
