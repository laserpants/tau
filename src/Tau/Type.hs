{-# LANGUAGE StrictData        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type where

import Data.Map.Strict (Map)
import Data.Set.Monad (Set, singleton, union, (\\))
import Tau.Core
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

-- | Type to represent types
data Type
    = TCon Name            -- ^ Type constructor
    | TVar Name            -- ^ Type variable
    | TArr Type Type       -- ^ Type of functions
    | TApp Type Type       -- ^ Type application
    deriving (Show, Eq)

-- | Built-in primitive types
tInt, tInteger, tBool, tFloat, tString, tChar, tUnit, tVoid :: Type

tInt     = TCon "Int"      -- ^ Int
tInteger = TCon "Integer"  -- ^ Integer
tBool    = TCon "Bool"     -- ^ Bool
tFloat   = TCon "Float"    -- ^ Float
tString  = TCon "String"   -- ^ String
tChar    = TCon "Char"     -- ^ Char
tUnit    = TCon "Unit"     -- ^ Unit
tVoid    = TCon "Void"     -- ^ Void

data Kind
    = Arrow Kind Kind      -- ^ Type arrow
    | Star                 -- ^ Concrete type
    deriving (Show, Eq)

data Scheme = Forall [Name] Type
    deriving (Show, Eq)

newtype Context = Context (Map Name Scheme)
    deriving (Show, Eq)

class Free t where
    free :: t -> Set Name

instance Free Type where
    free (TVar var)   = singleton var
    free (TArr t1 t2) = free t1 `union` free t2
    free (TApp t1 t2) = free t1 `union` free t2
    free _            = mempty

instance Free t => Free [t] where
    free = foldr (union . free) mempty

instance Free Scheme where
    free (Forall vars ty) = free ty \\ Set.fromList vars

instance Free Context where
    free (Context env) = free (Map.elems env)
