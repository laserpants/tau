module Utils 
  ( module Data.Text
  , prettyString
  ) where

import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Util (prettyPrint)

prettyString :: (Pretty p) => p -> String
prettyString = unpack . prettyPrint
