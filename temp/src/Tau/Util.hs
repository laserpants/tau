{-# LANGUAGE StrictData #-}
module Tau.Util where

import Data.Text (Text)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import qualified Data.Text.Lazy as Text (toStrict)

type Name = Text

nameSupply :: Text -> [Name]
nameSupply prefix = (prefix <>) . toText <$> nats
  where
    nats   = [1..] :: [Integer]
    toText = Text.toStrict . toLazyText . decimal

type Algebra f a = f a -> a
