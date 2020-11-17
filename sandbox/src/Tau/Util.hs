module Tau.Util 
  ( module Data.Eq.Deriving
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Debug.Trace
  , module Text.Show.Deriving
  , Name
  , Algebra
  ) where

import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Ord.Deriving
import Text.Show.Deriving
import Debug.Trace

type Name = String

type Algebra f a = f a -> a
