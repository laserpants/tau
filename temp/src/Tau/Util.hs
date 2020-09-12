{-# LANGUAGE StrictData #-}
module Tau.Util 
  ( module Data.Functor.Foldable
  , module Debug.Trace
  , Name
  , Algebra
  , nameSupply
  , prettyPrint
  , to3
  ) where

import Data.Functor.Foldable
import Data.Text (Text)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Debug.Trace
import qualified Data.Text.Lazy as Text (toStrict)

type Name = Text

nameSupply :: Text -> [Name]
nameSupply prefix = (prefix <>) . pack <$> nats
  where
    nats = [1..] :: [Integer]
    pack = Text.toStrict . toLazyText . decimal

type Algebra f a = f a -> a

prettyPrint :: (Pretty p) => p -> Text
prettyPrint = renderStrict . layoutPretty defaultLayoutOptions . pretty

to3 :: ((a, b), c) -> (a, b, c)
to3 ((a, b), c) = (a, b, c)
