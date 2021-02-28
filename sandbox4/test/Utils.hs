module Utils where

import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty, pretty)
import Tau.Lang.Pretty
import Tau.Util (renderDoc)

prettyString :: (Pretty p) => p -> String
prettyString = unpack . renderDoc . pretty

prettyParString :: (Parens p, Pretty p) => p -> String
prettyParString a = unpack (renderDoc (addParens a (pretty a)))
