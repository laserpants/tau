module Tau.Util 
  ( module Data.Eq.Deriving
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Debug.Trace
  , module Text.Show.Deriving
  , Name
  , Algebra
  , unions
  , nameSupply
  ) where

import Control.Monad
import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Set.Monad (Set)
import Debug.Trace
import Text.Show.Deriving
import qualified Data.Set.Monad as Set

type Name = String

type Algebra f a = f a -> a

unions :: (Ord a) => [Set a] -> Set a
unions = foldr Set.union mempty

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z'] >>= (:[]) -- . pack

nameSupply :: String -> [Name]
nameSupply prefix = fmap (prefix <>) letters
