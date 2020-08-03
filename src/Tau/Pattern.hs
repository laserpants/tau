{-# LANGUAGE StrictData #-}
module Tau.Pattern where

import Tau.Prim
import Tau.Util

data Pattern
    = VarP Name              -- ^ Variable pattern
    | ConP Name [Pattern]    -- ^ Constuctor pattern
    | LitP Prim              -- ^ Literal pattern
    | AnyP                   -- ^ Wildcard pattern
    deriving (Show, Eq)
