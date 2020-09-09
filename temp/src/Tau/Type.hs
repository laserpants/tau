module Tau.Type where

import Data.Text (Text)
import Tau.Util

data Type 
    = ConT Name            -- ^ Type constructor
    | VarT Name            -- ^ Type variable
    | ArrT Type Type       -- ^ Function type
    | AppT Type Type       -- ^ Type application
    deriving (Show, Eq)

-- | Type-class constraint
data TyClass = TyCl Name Type
    deriving (Show, Eq)

-- | Type scheme (polymorphic type)
data Scheme = Forall [Name] [TyClass] Type
    deriving (Show, Eq)

data TypeError a
    = CannotSolve
    | UnificationError a
    deriving (Show, Eq)

data Kind
    = VarK Name            -- ^ Kind placeholder variable
    | ArrK Kind Kind       -- ^ Type-level function
    | StarK                -- ^ Concrete type
    deriving (Show, Eq)
