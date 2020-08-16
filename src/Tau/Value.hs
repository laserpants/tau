{-# LANGUAGE StrictData #-}
module Tau.Value where

import Data.Map.Strict (Map)
import GHC.Show (showSpace)
import Tau.Ast
import Tau.Core
import Tau.Prim

-- | The environment is a mapping from variables to values.
type Env m = Map Name (Value m)

-- | An expression evaluates to a primitive value, a fully applied data
-- constructor, or a function closure.
data Value m
    = Value Prim                           -- ^ Literal value
    | Data Name [Value m]                  -- ^ Applied data constructor
    | Closure Name (m (Value m)) ~(Env m)  -- ^ Function closure

instance Show (Value m) where
    showsPrec p (Value val) =
        showParen (p >= 11)
            $ showString "Value"
            . showSpace
            . showsPrec 11 val
    showsPrec p (Data name vals) =
        showParen (p >= 11)
            $ showString "Data"
            . showSpace
            . showsPrec 11 name
            . showSpace
            . showsPrec 11 vals
    showsPrec _ Closure{} =
        showString "<<function>>"
