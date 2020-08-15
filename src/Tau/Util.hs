{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}
module Tau.Util where

import Data.Eq.Deriving
import Data.Function ((&))
import Data.Text (Text)
import Text.Show.Deriving

type Name = Text

(|>) = (&)
($>) = (&)

infixl 1 |>
infixl 0 $>

type List = []

data (f :*: g) a = (:*:)
    { left  :: f a
    , right :: g a }
  deriving
    ( Eq
    , Show
    , Functor
    , Foldable
    , Traversable )

infixl 3 :*:

anyM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM p (x:xs) = do
    q <- p x
    if q then return True else anyM p xs

$(deriveShow1 ''(:*:))
$(deriveEq1   ''(:*:))
