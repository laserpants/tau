{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Util where

import Control.Monad.Except
import Control.Monad (replicateM)
import Control.Monad.Supply
import Data.Functor.Foldable
import Data.Text (Text, pack)

type Name = Text

type Algebra f a = f a -> a

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f = ((f <$>) <$>)

infixl 4 <$$>

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

letters :: [Text]
letters = pack <$> ([1..] >>= flip replicateM ['a'..'z'])

instance MonadSupply s f m => MonadSupply s f (ExceptT e m) where
    supply  = lift . supply
    provide = lift . provide

demands :: (MonadSupply a f m) => Int -> m [a]
demands n = replicateM n demand

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err Nothing = throwError err
liftMaybe _ (Just ok) = pure ok
