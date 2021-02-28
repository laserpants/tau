module Utils where

import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Lang.Pretty
import Tau.Util (prettyPrint)

prettyString :: (Pretty p) => p -> String
prettyString = unpack . prettyPrint

