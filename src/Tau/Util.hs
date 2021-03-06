{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}
module Tau.Util
  ( module Data.Functor.Foldable
  , module Debug.Trace
  , Name
  , Algebra
  , nameSupply
  , prettyPrint
  , to3
  , unpair
  , unpairs
  , liftMaybe
  , integerToText
  , intToText
  , letters
  , hasKey
  , (:*:)(..)
  ) where

import Control.Monad (replicateM)
import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Text (Text, pack)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Debug.Trace
import Text.Show.Deriving
import qualified Data.Text.Lazy as Text (toStrict)

type Name = Text

type Algebra f a = f a -> a

nameSupply :: Text -> [Name]
nameSupply prefix = (prefix <>) . integerToText <$> nats
  where
    nats = [1..] :: [Integer]

letters :: [Text]
letters = [1..] >>= flip replicateM ['a'..'z']
                >>= (:[]) . pack

integerToText :: Integer -> Text
integerToText = Text.toStrict . toLazyText . decimal

intToText :: Int -> Text
intToText = integerToText . fromIntegral

prettyPrint :: (Pretty p) => p -> Text
prettyPrint = renderStrict . layoutPretty defaultLayoutOptions . pretty

unpair :: (a, a) -> [a]
unpair (f, s) = [f, s]

unpairs :: [(a, a)] -> [a]
unpairs = concatMap unpair

to3 :: ((a, b), c) -> (a, b, c)
to3 ((a, b), c) = (a, b, c)

liftMaybe :: (MonadFail m) => String -> Maybe a -> m a
liftMaybe err Nothing = fail err
liftMaybe _ (Just ok) = pure ok

hasKey :: (Eq a) => a -> [(a, b)] -> Bool
hasKey a xs = a `elem` (fst <$> xs)

data (f :*: g) a = (:*:)
    { left  :: f a
    , right :: g a }
  deriving
    ( Eq
    , Show
    , Functor
    , Foldable
    , Traversable )

$(deriveShow1 ''(:*:))
$(deriveEq1   ''(:*:))
