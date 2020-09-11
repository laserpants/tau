import Tau.TypeUnificationTests
import Tau.ParserTests
import Test.Hspec

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
        describe "\nParser\n" testParser
