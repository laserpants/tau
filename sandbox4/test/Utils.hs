{-# LANGUAGE OverloadedStrings #-}
module Utils where

import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty, pretty)
import Tau.Lang.Pretty
import Tau.Lang.Type
import Tau.Util (renderDoc)

prettyString :: (Pretty p) => p -> String
prettyString = unpack . renderDoc . pretty

prettyParString :: (Parens p, Pretty p) => p -> String
prettyParString a = unpack (renderDoc (addParens a))

_a :: Type
_a = tVar kTyp "a"

_b :: Type
_b = tVar kTyp "b"
