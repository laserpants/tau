{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Type where

import Data.Eq.Deriving
import Data.Text (Text)
import Tau.Util
import Text.Show.Deriving

data TypeF  a
    = ConT Name            -- ^ Type constructor
    | VarT Name            -- ^ Type variable
    | ArrT a a             -- ^ Function type
    | AppT a a             -- ^ Type application
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Type = Fix TypeF

$(deriveShow1 ''TypeF)
$(deriveEq1   ''TypeF)

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

data KindF a
    = VarK Name            -- ^ Kind placeholder variable
    | ArrK a a             -- ^ Type-level function
    | StarK                -- ^ Concrete type
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Kind = Fix KindF

$(deriveShow1 ''KindF)
$(deriveEq1   ''KindF)

conT :: Name -> Type
conT = Fix . ConT

varT :: Name -> Type
varT = Fix . VarT

arrT :: Type -> Type -> Type
arrT a1 a2 = Fix (ArrT a1 a2)

appT :: Type -> Type -> Type
appT a1 a2 = Fix (AppT a1 a2)

varK :: Name -> Kind
varK = Fix . VarK

arrK :: Kind -> Kind -> Kind
arrK a1 a2 = Fix (ArrK a1 a2)

starK :: Kind
starK = Fix StarK

tInt, tInteger, tBool, tFloat, tString, tChar, tUnit, tVoid :: Type

tInt     = conT "Int"      -- ^ Int
tInteger = conT "Integer"  -- ^ Integer
tBool    = conT "Bool"     -- ^ Bool
tFloat   = conT "Float"    -- ^ Float
tString  = conT "String"   -- ^ String
tChar    = conT "Char"     -- ^ Char
tUnit    = conT "Unit"     -- ^ Unit
tVoid    = conT "Void"     -- ^ Void
