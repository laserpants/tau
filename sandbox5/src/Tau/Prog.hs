{-# LANGUAGE StrictData #-}
module Tau.Prog where

import Data.Set.Monad (Set)
import Tau.Env (Env(..))
import Tau.Lang
import Tau.Tool
import Tau.Type

-- | Product type
data Product = Mul Name [Type]
    deriving (Show, Eq, Ord)

-- | Sum type
data Datatype = Sum Name [Name] [Product]
    deriving (Show, Eq, Ord)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Context = Env (Set Name)

-- TODO
type ClassInfo a b = a

type TypeEnv = Env Scheme

type ClassEnv = Env (ClassInfo Name Type, ClassInfo Type (Ast TypeInfo))
