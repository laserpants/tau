{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
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
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Pattern = Fix PatternF

-- VarP constructor
varP :: Name -> Pattern
varP = Fix . VarP

-- ConP constructor
conP :: Name -> [Pattern] -> Pattern
conP a = Fix . ConP a

-- LitP constructor
litP :: Prim -> Pattern
litP = Fix . LitP

-- AnyP constructor
anyP :: Pattern
anyP = Fix AnyP

$(deriveShow1 ''PatternF)
$(deriveEq1   ''PatternF)
