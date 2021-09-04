{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Util where

import Control.Monad (replicateM)
import Control.Monad.Except (MonadError, ExceptT, throwError)
import Control.Monad.State (MonadState, get, put)
import Control.Monad.Supply (SupplyT, Supply, evalSupplyT, evalSupply)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Functor.Foldable (Base, Corecursive, embed)
import Data.Maybe (fromJust)
import Data.Text (Text, pack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text

type Name = Text

type Algebra   f a = f a -> a
type Coalgebra f a = a -> f a

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f = ((f <$>) <$>)

infixl 4 <$$>

embed1 :: (Corecursive t) => (t1 -> Base t t) -> t1 -> t
embed1 t a = embed (t a)
{-# INLINE embed1 #-}

embed2 :: (Corecursive t) => (t1 -> t2 -> Base t t) -> t1 -> t2 -> t
embed2 t a b = embed (t a b)
{-# INLINE embed2 #-}

embed3 :: (Corecursive t) => (t1 -> t2 -> t3 -> Base t t) -> t1 -> t2 -> t3 -> t
embed3 t a b c = embed (t a b c)
{-# INLINE embed3 #-}

embed4 :: (Corecursive t) => (t1 -> t2 -> t3 -> t4 -> Base t t) -> t1 -> t2 -> t3 -> t4 -> t
embed4 t a b c d = embed (t a b c d)
{-# INLINE embed4 #-}

embed5 :: (Corecursive t) => (t1 -> t2 -> t3 -> t4 -> t5 -> Base t t) -> t1 -> t2 -> t3 -> t4 -> t5 -> t
embed5 t a b c d e = embed (t a b c d e)
{-# INLINE embed5 #-}

letters :: [Text]
letters = pack <$> ([1..] >>= flip replicateM ['a'..'z'])

liftMaybe :: (MonadError e m) => e -> Maybe a -> m a
liftMaybe err Nothing = throwError err
liftMaybe _ (Just ok) = pure ok

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither = flip maybe Right . Left
{-# INLINE maybeToEither #-}

getAndReset :: (Monoid a, MonadState a m) => m a
getAndReset = get <* put mempty
{-# INLINE getAndReset #-}

nats :: [Int]
nats = enumFrom 0
{-# INLINE nats #-}

runSupplyNats :: Supply Int a -> a
runSupplyNats = fromJust . flip evalSupply nats

runSupplyNatsT :: (Monad m) => SupplyT Int (MaybeT m) a -> m a
runSupplyNatsT = fmap fromJust . runMaybeT . flip evalSupplyT nats

-------------------------------------------------------------------------------

renderDoc :: Doc a -> Text
renderDoc = renderStrict . layoutPretty defaultLayoutOptions

renderDocW :: Int -> Doc a -> Text
renderDocW w = renderStrict . layoutPretty layoutOptions where
    layoutOptions =
        LayoutOptions { layoutPageWidth = AvailablePerLine w 1 }

prettyT :: (Pretty p) => p -> Text
prettyT = renderDoc . pretty
{-# INLINE prettyT #-}

prettyW :: (Pretty p) => Int -> p -> Text
prettyW w = renderDocW w . pretty
{-# INLINE prettyW #-}
