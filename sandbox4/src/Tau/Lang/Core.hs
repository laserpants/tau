{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Lang.Core where

import Tau.Lang.Expr
import Tau.Util

data CoreF a
    = CVar Name                 -- ^ Variable
    | CLit Literal              -- ^ Literal value
    | CApp [a]                  -- ^ Function application
    | CLet Name a a             -- ^ Let expression
    | CLam Name a               -- ^ Lambda abstraction
    | CIf a ~a ~a               -- ^ If-clause
--    | CPat a [Clause Name a]    -- ^ Pattern matching clause-matrix
    | CPat a [([Name], a)]      -- ^ Pattern matching clause-matrix
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''CoreF
deriveEq1   ''CoreF

type Core = Fix CoreF

cVar :: Name -> Core
cVar = embed1 CVar

cLit :: Literal -> Core
cLit = embed1 CLit

cApp :: [Core] -> Core
cApp = embed1 CApp

cLet :: Name -> Core -> Core -> Core
cLet = embed3 CLet

cLam :: Name -> Core -> Core
cLam = embed2 CLam

cIf :: Core -> Core -> Core -> Core
cIf = embed3 CIf

--cPat :: Core -> [Clause Name Core] -> Core
--cPat = embed2 CPat

cPat :: Core -> [([Name], Core)] -> Core
cPat = embed2 CPat
