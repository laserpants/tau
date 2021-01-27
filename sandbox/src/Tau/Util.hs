{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Tau.Util 
  ( module Data.Eq.Deriving
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Debug.Trace
  , module Data.Types.Injective
  , module Text.Show.Deriving
  , Name
  , Algebra
  , unions
  , nameSupply
  , numSupply
  , debug
  , first3M
  , second3M
  , third3M
  , integerToText
  , intToText
  , prettyPrint
  ) where

import Control.Monad
import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Set.Monad (Set)
import Data.Text (Text, pack)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Types.Injective
import Debug.Trace
import System.IO.Unsafe
import Text.Show.Deriving
import qualified Data.Set.Monad as Set
import qualified Data.Text.Lazy as Text (toStrict)

type Name = Text

type Algebra f a = f a -> a

unions :: (Ord a) => [Set a] -> Set a
unions = foldr Set.union mempty

letters :: [Text]
letters = pack <$> fn where
    fn = [1..] >>= flip replicateM ['a'..'z']

prefixSupply :: [Text] -> Text -> [Name]
prefixSupply supply prefix = fmap (prefix <>) supply

nameSupply :: Text -> [Name]
nameSupply = prefixSupply letters

numSupply :: Text -> [Name]
numSupply = prefixSupply (pack . show <$> [1..])

debug :: (Monad m) => String -> m ()
debug info = case unsafePerformIO (putStrLn info) of () -> pure ()

instance Injective ((a, b), c) (a, b, c) where
    to ((a, b), c) = (a, b, c) 

instance Injective (a, (b, c)) (a, b, c) where
    to (a, (b, c)) = (a, b, c)

first3M :: (Monad m) => (a -> m a1) -> (a, b, c) -> m (a1, b, c)
first3M f (a, b, c) = do
    a1 <- f a
    pure (a1, b, c)

second3M :: (Monad m) => (b -> m b1) -> (a, b, c) -> m (a, b1, c)
second3M f (a, b, c) = do
    b1 <- f b
    pure (a, b1, c)

third3M :: (Monad m) => (c -> m c1) -> (a, b, c) -> m (a, b, c1)
third3M f (a, b, c) = do
    c1 <- f c
    pure (a, b, c1)

integerToText :: Integer -> Text
integerToText = Text.toStrict . toLazyText . decimal

intToText :: Int -> Text
intToText = integerToText . fromIntegral

prettyPrint :: (Pretty p) => p -> Text
prettyPrint = renderStrict . layoutPretty defaultLayoutOptions . pretty
