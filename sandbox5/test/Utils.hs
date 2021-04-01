{-# LANGUAGE OverloadedStrings #-}
module Utils 
  ( module Debug.Trace
  , describe
  , it
  , _a
  , _b
  , _c
  , renderDoc
  , prettyText
  ) where

import Data.Text (Text, unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Debug.Trace
import Tau.Type
import Test.Hspec hiding (describe, it) 
import qualified Test.Hspec as Hspec

describe :: Text -> SpecWith () -> SpecWith ()
describe = Hspec.describe . unpack

it :: (Example a) => Text -> a -> SpecWith (Arg a)
it = Hspec.it . unpack

_a :: Type
_a = tVar kTyp "a"

_b :: Type
_b = tVar kTyp "b"

_c :: Type
_c = tVar kTyp "c"

renderDoc :: Doc a -> Text
renderDoc = renderStrict . layoutPretty defaultLayoutOptions

prettyText :: (Pretty p) => p -> Text
prettyText = renderDoc . pretty
