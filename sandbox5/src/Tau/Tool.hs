module Tau.Tool 
  ( Name
  , Algebra
  , List
  , (<$$>)
  , pluck
  , liftMaybe
  , embed1
  , embed2
  , embed3
  , embed4
  , embed5
  , intToText
  , integerToText
  , letters
  , nameSupply
  , numSupply
  , prettyPrint
  , module Data.Eq.Deriving
  , module Data.Fix
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Data.Text
  , module Data.Void
  , module Debug.Trace
  , module Text.Show.Deriving
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Eq.Deriving
import Data.Fix (Fix(..))
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Text (Text, pack)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Void
import Debug.Trace
import Text.Show.Deriving
import qualified Data.Text.Lazy as Text (toStrict)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Internal tooling
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type List = []

type Name = Text

type Algebra f a = f a -> a

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f = ((f <$>) <$>)

infixl 4 <$$>

pluck :: (Monoid a, MonadState a m) => m a
pluck = do
    a <- get
    put mempty
    pure a

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err Nothing = throwError err
liftMaybe _ (Just ok) = pure ok

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

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

integerToText :: Integer -> Text
integerToText = Text.toStrict . toLazyText . decimal

intToText :: Int -> Text
intToText = integerToText . fromIntegral

letters :: [Text]
letters = pack <$> ([1..] >>= flip replicateM ['a'..'z'])

prefixed :: [Text] -> Text -> [Name]
prefixed suppls prefix = fmap (prefix <>) suppls

nameSupply :: Text -> [Name]
nameSupply = prefixed letters

numSupply :: Text -> [Name]
numSupply = prefixed (intToText <$> [1..])

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

renderDoc :: Doc a -> Text
renderDoc = renderStrict . layoutPretty defaultLayoutOptions

prettyPrint :: (Pretty p) => p -> Text
prettyPrint = renderDoc . pretty
