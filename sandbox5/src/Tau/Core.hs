{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Core where

import Tau.Lang (Prim)
import Tau.Util

type CMatrix a = List ([Name], a)

data CoreF a
    = CVar Name                 -- ^ Variable
    | CLit Prim                 -- ^ Primitive value
    | CApp [a]                  -- ^ Function application
    | CLet Name a a             -- ^ Let expression
    | CLam Name a               -- ^ Lambda abstraction
    | CIf  a ~a ~a              -- ^ If-clause
    | CPat a (CMatrix a)        -- ^ Pattern match clause matrix

-- | Core language expression used for interpreted program evaluation and code 
-- generation
type Core = Fix CoreF

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Type class instances for Core

deriving instance (Show a) => Show (CoreF a)
deriving instance (Eq   a) => Eq   (CoreF a)
deriving instance (Ord  a) => Ord  (CoreF a)

deriveShow1 ''CoreF
deriveEq1   ''CoreF
deriveOrd1  ''CoreF

deriving instance Functor     CoreF
deriving instance Foldable    CoreF
deriving instance Traversable CoreF

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Constructors
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

cVar :: Name -> Core
cVar = embed1 CVar

cLit :: Prim -> Core
cLit = embed1 CLit

cApp :: [Core] -> Core
cApp = embed1 CApp

cLet :: Name -> Core -> Core -> Core
cLet = embed3 CLet

cLam :: Name -> Core -> Core
cLam = embed2 CLam

cIf :: Core -> Core -> Core -> Core
cIf = embed3 CIf

cPat :: Core -> CMatrix Core -> Core
cPat = embed2 CPat
