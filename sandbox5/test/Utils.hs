module Utils where

import Data.Text (Text, unpack)
import Test.Hspec

describeTest :: Text -> SpecWith () -> SpecWith ()
describeTest = describe . unpack
