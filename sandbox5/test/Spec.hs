import Tau.TypeTests
import Test.Hspec
import Utils

main :: IO ()
main =
    hspec $ do
        describeTest "Types" testTypes
        describeTest "Tau.Type.kindOf" testKindOf
