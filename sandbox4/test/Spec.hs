import Test.Hspec
import Tau.TypeUnificationTests

main :: IO ()
main =
    hspec $ do
        describe "\nType unification\n" testTypeUnification
--        describe "\nType substitution\n" testSubstitute
