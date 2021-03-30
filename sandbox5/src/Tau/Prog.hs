{-# LANGUAGE StrictData #-}
module Tau.Prog where

import Tau.Tool
import Tau.Type

-- | Product type
data Product = Mul Name [Type]
    deriving (Show, Eq, Ord)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq, Ord)
