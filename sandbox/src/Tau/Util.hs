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
  ) where

import Control.Monad
import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Set.Monad (Set)
import Data.Text (Text, pack)
import Data.Types.Injective
import Debug.Trace
import System.IO.Unsafe
import Text.Show.Deriving
import qualified Data.Set.Monad as Set

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
