{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Type where

import Control.Arrow ((>>>))
import Control.Monad
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Tuple.Extra (first)
import Tau.Tooling
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

data KindF a
    = KVar Name
    | KCon Name
    | KArr a a 

-- | Kind
type Kind = Fix KindF

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data TypeF k i a 
    = TVar k Name             -- ^ Type variable
    | TCon k Name             -- ^ Type constructor
    | TRow Name a a           -- ^ Row type
    | TApp k a a              -- ^ Type application
    | TArr a a                -- ^ Function type
    | TGen i                  -- ^ Quantified type variable

-- | Type 
type TypeT i = Fix (TypeF Kind i)

-- | Standalone type (a type that is not embedded in a type scheme)
type Type = TypeT Void

-- | A type which appears in a type scheme and therefore may contain quantified 
-- variables
type Polytype = TypeT Int

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Type class constraint
data PredicateT a = InClass Name a

-- | A standalone type class constraint
type Predicate = PredicateT Type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Polymorphic type scheme
data Scheme = Forall [Kind] [PredicateT Int] Polytype

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Class of data types that carry type information
class Typed a where
    typeOf :: a -> Type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Class of data types that contain free type variables
class FreeIn t where
    free :: t -> [(Name, Kind)]

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Type class instances for Kind

deriving instance (Show a) => 
    Show (KindF a)

deriving instance (Eq a) => 
    Eq (KindF a)

deriving instance (Ord a) => 
    Ord (KindF a)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

deriving instance Functor     KindF
deriving instance Foldable    KindF
deriving instance Traversable KindF

-- Type class instances for Type

deriving instance (Show k, Show i, Show a) => 
    Show (TypeF k i a)

deriving instance (Eq k, Eq i, Eq a) => 
    Eq (TypeF k i a)

deriving instance (Ord k, Ord i, Ord a) => 
    Ord (TypeF k i a)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

deriving instance Functor     (TypeF k i)
deriving instance Foldable    (TypeF k i)
deriving instance Traversable (TypeF k i)

-- Type class instances for Predicate

deriving instance (Show a) => 
    Show (PredicateT a)

deriving instance (Eq a) => 
    Eq (PredicateT a)

deriving instance (Ord a) => 
    Ord (PredicateT a)

deriveShow1 ''PredicateT
deriveEq1   ''PredicateT
deriveOrd1  ''PredicateT

deriving instance Functor     PredicateT
deriving instance Foldable    PredicateT
deriving instance Traversable PredicateT

-- Type class instances for Scheme

deriving instance Show Scheme
deriving instance Eq Scheme 
deriving instance Ord Scheme

-- Typed instances

instance Typed Type where
    typeOf = id

-- FreeIn instances

instance (FreeIn t) => FreeIn [t] where
    free = concatMap free

instance FreeIn (TypeT a) where
    free = typeVars

instance FreeIn Scheme where
    free (Forall _ _ t) = free t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

getKindVar :: Kind -> Maybe Name
getKindVar = project >>> \case
    KVar v   -> Just v
    _        -> Nothing

getKindCon :: Kind -> Maybe Name
getKindCon = project >>> \case
    KCon c   -> Just c
    _        -> Nothing

isVar :: Type -> Bool
isVar = project >>> \case
    TVar{}   -> True
    _        -> False

isCon :: Type -> Bool
isCon = project >>> \case
    TCon{}   -> True
    _        -> False

getTypeVar :: Type -> Maybe Name
getTypeVar = project >>> \case
    TVar _ v -> Just v
    _        -> Nothing

getTypeIndex :: Polytype -> Maybe Int
getTypeIndex = project >>> \case
    TGen i   -> Just i
    _        -> Nothing

--isListType :: Type -> Bool
--isListType = project >>> \case
--    TApp _ a _ -> 
--        case project a of
--            TCon _ "List" -> True
--            _ -> False
--    _         -> False
--
--isTupleType :: Type -> Bool
--isTupleType ty = Just True == maybeIsTupleCon
--  where
--    maybeIsTupleCon = Text.all (== ',') <$> (stripped <=< leftmost) ty
--    stripped        = Text.stripSuffix ")" <=< Text.stripPrefix "("
--
--    leftmost :: Type -> Maybe Name
--    leftmost = cata $ \case
--        TCon _ con   -> Just con
--        TApp _ a _   -> a
--        _            -> Nothing

kindOf :: Type -> Kind
kindOf = project >>> \case
    TVar a _     -> a
    TCon a _     -> a
    TApp a _ _   -> a
    TArr{}       -> kTyp
    TRow{}       -> kRow

kindVars :: Kind -> [Name]
kindVars = nub . cata (\case
    KVar var     -> [var]
    KArr k1 k2   -> k1 <> k2
    _            -> [])

typeVars :: TypeT a -> [(Name, Kind)]
typeVars = nub . cata (\case
    TVar k var   -> [(var, k)]
    TApp _ t1 t2 -> t1 <> t2
    TArr t1 t2   -> t1 <> t2
    _            -> [])

toPolytype :: Type -> Polytype
toPolytype = cata $ \case
    TVar k var   -> tVar k var
    TCon k con   -> tCon k con
    TApp k t1 t2 -> tApp k t1 t2
    TArr t1 t2   -> tArr t1 t2
    TRow n t1 t2 -> tRow n t1 t2 

fromPolytype :: [Type] -> Polytype -> Type
fromPolytype ts = cata $ \case
    TGen n       -> ts !! n
    TApp k t1 t2 -> tApp k t1 t2
    TVar k var   -> tVar k var
    TCon k con   -> tCon k con
    TArr t1 t2   -> tArr t1 t2
    TRow n t1 t2 -> tRow n t1 t2

toScheme :: Type -> Scheme
toScheme = Forall [] [] . toPolytype

tupleCon :: Int -> Name
tupleCon size = "(" <> Text.replicate (pred size) "," <> ")"

predicateName :: PredicateT a -> Name
predicateName (InClass name _) = name

predicateType :: PredicateT a -> a
predicateType (InClass _ t) = t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Constructors
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Kind

kVar :: Name -> Kind 
kVar = embed1 KVar

kCon :: Name -> Kind 
kCon = embed1 KCon

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr

kTyp :: Kind
kTyp = kCon "*"

kClass :: Kind
kClass = kCon "Constraint"

kRow :: Kind
kRow = kCon "Row"

infixr 1 `kArr`

kFun :: Kind
kFun = kTyp `kArr` kTyp

kFun2 :: Kind
kFun2 = kTyp `kArr` kTyp `kArr` kTyp

-- Type

tVar :: Kind -> Name -> TypeT a
tVar = embed2 TVar

tGen :: a -> TypeT a
tGen = embed1 TGen

tCon :: Kind -> Name -> TypeT a
tCon = embed2 TCon

tArr :: TypeT a -> TypeT a -> TypeT a
tArr = embed2 TArr

infixr 1 `tArr`

tApp :: Kind -> TypeT a -> TypeT a -> TypeT a
tApp = embed3 TApp

tRow :: Name -> TypeT a -> TypeT a -> TypeT a
tRow = embed3 TRow

typ :: Name -> TypeT a
typ = tCon kTyp

-- Built-in types

tVoid :: TypeT a
tVoid = typ "Void"

tUnit :: TypeT a
tUnit = typ "Unit"

tBool :: TypeT a
tBool = typ "Bool"

tNat :: TypeT a
tNat = typ "Nat"

tInt :: TypeT a
tInt = typ "Int"

tInteger :: TypeT a
tInteger = typ "Integer"

tFloat :: TypeT a
tFloat = typ "Float"

tDouble :: TypeT a
tDouble = typ "Double"

tChar :: TypeT a
tChar = typ "Char"

tString :: TypeT a
tString = typ "String"

-- Lists

tListCon :: TypeT a
tListCon = tCon kFun "List"

tList :: TypeT a -> TypeT a
tList = tApp kTyp tListCon

-- Tuples

tTupleCon :: Int -> TypeT a
tTupleCon n = tCon (foldr kArr kTyp (replicate n kTyp)) (tupleCon n)

tTuple :: [TypeT a] -> TypeT a
tTuple types = foldl (tApp kTyp) (tTupleCon (length types)) types

tPair :: TypeT a -> TypeT a -> TypeT a
tPair t1 t2 = tTuple [t1, t2]

tTriple :: TypeT a -> TypeT a -> TypeT a -> TypeT a
tTriple t1 t2 t3 = tTuple [t1, t2, t3]

-- Rows

tRowNil :: TypeT a
tRowNil = tCon kRow "{}"

-- Records

tRecordCon :: TypeT a
tRecordCon = tCon (kArr kRow kTyp) "#"

tRecord :: TypeT a -> TypeT a
tRecord = tApp kTyp tRecordCon 
