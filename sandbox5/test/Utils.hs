{-# LANGUAGE OverloadedStrings #-}
module Utils where

import Data.Text (Text, unpack)
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
