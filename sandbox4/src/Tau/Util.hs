{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Tau.Util 
  ( module Data.Eq.Deriving
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Debug.Trace
  , module Data.Fix
  , module Data.Text.Prettyprint.Doc
  , module Data.Types.Injective
  , module Text.Show.Deriving
  , Name
  , Algebra
  , (<$$>)
  , debugLog
  , embed1
  , embed2
  , embed3
  , embed4
  , embed5
  , first3M
  , firstM
  , intToText
  , integerToText
  , letters
  , nameSupply
  , numSupply
  , prettyPrint
  , renderDoc
  , reset
  , second3M
  , secondM
  , third3M
  , liftMaybe
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Eq.Deriving
import Data.Fix (Fix(..))
import Data.Functor.Foldable
import Data.List (unfoldr)
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

letters :: [Text]
letters = pack <$> ([1..] >>= flip replicateM ['a'..'z'])

prefixed :: [Text] -> Text -> [Name]
prefixed suppls prefix = fmap (prefix <>) suppls

nameSupply :: Text -> [Name]
nameSupply = prefixed letters

numSupply :: Text -> [Name]
numSupply = prefixed (intToText <$> [1..])

debugLog :: (Monad m) => String -> m ()
debugLog str = case unsafePerformIO (putStrLn str) of () -> pure ()

instance Injective ((a, b), c) (a, b, c) where
    to ((a, b), c) = (a, b, c) 

instance Injective (a, (b, c)) (a, b, c) where
    to (a, (b, c)) = (a, b, c)

firstM :: (Monad m) => (a -> m a1) -> (a, b) -> m (a1, b)
firstM f (a, b) = do
    a1 <- f a
    pure (a1, b)

secondM :: (Monad m) => (b -> m b1) -> (a, b) -> m (a, b1)
secondM f (a, b) = do
    b1 <- f b
    pure (a, b1)

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

integerToText :: Integer -> Text
integerToText = Text.toStrict . toLazyText . decimal

intToText :: Int -> Text
intToText = integerToText . fromIntegral

renderDoc :: Doc a -> Text
renderDoc = renderStrict . layoutPretty -- defaultLayoutOptions
    (LayoutOptions { layoutPageWidth = AvailablePerLine 40 1.0 })

prettyPrint :: (Pretty p) => p -> Text
prettyPrint = renderDoc . pretty

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f = ((f <$>) <$>)

infixl 4 <$$>

reset :: (Monoid a, MonadState a m) => m a
reset = do
    a <- get
    put mempty
    pure a

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err Nothing = throwError err
liftMaybe _ (Just ok) = pure ok
