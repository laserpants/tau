module Tau.Tool 
  ( Name
  , Algebra
  , (<$$>)
  , embed1
  , embed2
  , embed3
  , embed4
  , embed5
  , module Data.Eq.Deriving
  , module Data.Fix
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Data.Text
  , module Data.Void
  , module Text.Show.Deriving
  ) where

import Data.Eq.Deriving
import Data.Fix (Fix(..))
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Text (Text)
import Data.Void
import Text.Show.Deriving

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Internal tooling
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Name = Text

type Algebra f a = f a -> a

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f = ((f <$>) <$>)

infixl 4 <$$>

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

embed1 :: (Corecursive t) => (t1 -> Base t t) -> t1 -> t
embed1 t a = embed (t a)

embed2 :: (Corecursive t) => (t1 -> t2 -> Base t t) -> t1 -> t2 -> t
embed2 t a b = embed (t a b)

embed3 :: (Corecursive t) => (t1 -> t2 -> t3 -> Base t t) -> t1 -> t2 -> t3 -> t
embed3 t a b c = embed (t a b c)

embed4 :: (Corecursive t) => (t1 -> t2 -> t3 -> t4 -> Base t t) -> t1 -> t2 -> t3 -> t4 -> t
embed4 t a b c d = embed (t a b c d)

embed5 :: (Corecursive t) => (t1 -> t2 -> t3 -> t4 -> t5 -> Base t t) -> t1 -> t2 -> t3 -> t4 -> t5 -> t
embed5 t a b c d e = embed (t a b c d e)
