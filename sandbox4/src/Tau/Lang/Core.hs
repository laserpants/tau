{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Lang.Core where

import Tau.Lang.Expr
import Tau.Util

data Rep 
    = RVar Name               -- ^ Simple variable pattern
    | RCon Name [Name]        -- ^ Simple constuctor pattern
    deriving (Show, Eq)

data CoreF a
    = CVar Name               -- ^ Variable
    | CLit Literal            -- ^ Literal value
    | CApp [a]                -- ^ Function application
    | CLet Name a a           -- ^ Let expression
    | CLam Name a             -- ^ Lambda abstraction
    | CIf a ~a ~a             -- ^ If-clause
    | CPat [a] [Clause Rep a] -- ^ Pattern matching clause-matrix
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''CoreF
deriveEq1   ''CoreF

type Core = Fix CoreF
