{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Pattern where

import Data.Eq.Deriving
import Data.Functor.Foldable
import Tau.Prim
import Tau.Util
import Text.Show.Deriving

data PatternF a
    = VarP Name              -- ^ Variable pattern
    | ConP Name [a]          -- ^ Constuctor pattern
    | LitP Prim              -- ^ Literal pattern
    | AnyP                   -- ^ Wildcard pattern
    deriving (Show, Eq)

type Pattern = Fix PatternF

$(deriveShow1 ''PatternF)
$(deriveEq1   ''PatternF)
