{-# LANGUAGE StrictData #-}
module Tau.Prim where

import Data.Text (Text)

-- | Language primitives
data Prim
    = Unit                   -- ^ Unit value
    | Bool Bool              -- ^ Boolean
    | Int Int                -- ^ Machine-level integers (32 or 64 bit)
    | Integer Integer        -- ^ Arbitrary precision integer
    | Float Double           -- ^ Floating point number
    | Char Char              -- ^ Char
    | String Text            -- ^ String
    deriving (Show, Eq)
