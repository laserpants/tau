{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Tau.Tooling
  -- Util
  ( Name
  , Algebra
  , List
  , (<$$>)
  , getAndReset
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
  , renderDoc
  , prettyPrint
  , whenLeft
  , firstM
  , secondM
--  , first3M
--  , second3M
--  , third3M
  , module Control.Arrow
  , module Data.Eq.Deriving
  , module Data.Fix
  , module Data.Functor.Foldable
  , module Data.Ord.Deriving
  , module Data.Text
  , module Data.Text.Prettyprint.Doc
  , module Data.Types.Injective
  , module Data.Void
  , module Debug.Trace
  , module Text.Show.Deriving
  ) where

import Control.Arrow ((<<<), (>>>), (***), (&&&))
import Control.Monad.Except
import Control.Monad.State
import Data.Eq.Deriving
import Data.Fix (Fix(..))
import Data.Functor.Foldable
import Data.Ord.Deriving
import Data.Text (Text, pack)
import Data.Tuple.Extra (firstM, secondM)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Types.Injective
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

getAndReset :: (Monoid a, MonadState a m) => m a
getAndReset = get <* put mempty

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err Nothing = throwError err
liftMaybe _ (Just ok) = pure ok

whenLeft :: (Monad m) => (a -> m ()) -> Either a () -> m ()
whenLeft run = \case 
    Left err -> run err
    Right () -> pure ()

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Injective ((a, b), c) (a, b, c) where
    to ((a, b), c) = (a, b, c) 

instance Injective (a, (b, c)) (a, b, c) where
    to (a, (b, c)) = (a, b, c)

instance Injective ((a, b, c), d) (a, b, c, d) where
    to ((a, b, c), d) = (a, b, c, d)

instance Injective (a, (b, c, d)) (a, b, c, d) where
    to (a, (b, c, d)) = (a, b, c, d)

instance Injective ((a, b), c, d) (a, b, c, d) where
    to ((a, b), c, d) = (a, b, c, d)

instance Injective (a, (b, c), d) (a, b, c, d) where
    to (a, (b, c), d) = (a, b, c, d)

instance Injective (a, b, (c, d)) (a, b, c, d) where
    to (a, b, (c, d)) = (a, b, c, d)

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

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--firstM :: (Monad m) => (a -> m a1) -> (a, b) -> m (a1, b)
--firstM f (a, b) = do
--    a1 <- f a
--    pure (a1, b)
--
--secondM :: (Monad m) => (b -> m b1) -> (a, b) -> m (a, b1)
--secondM f (a, b) = do
--    b1 <- f b
--    pure (a, b1)
--
--first3M :: (Monad m) => (a -> m a1) -> (a, b, c) -> m (a1, b, c)
--first3M f (a, b, c) = do
--    a1 <- f a
--    pure (a1, b, c)
--
--second3M :: (Monad m) => (b -> m b1) -> (a, b, c) -> m (a, b1, c)
--second3M f (a, b, c) = do
--    b1 <- f b
--    pure (a, b1, c)
--
--third3M :: (Monad m) => (c -> m c1) -> (a, b, c) -> m (a, b, c1)
--third3M f (a, b, c) = do
--    c1 <- f c
--    pure (a, b, c1)
