{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Type where

import Control.Arrow ((>>>))
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Tuple.Extra (first)
import Tau.Row
import Tau.Tool
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

data KindF a
    = KTyp                    -- ^ Concrete (value) types
    | KArr a a                -- ^ Type constructors
    | KClass                  -- ^ Type class constraints
    | KRow                    -- ^ Rows

-- | Kind
type Kind = Fix KindF

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

data TypeF i a 
    = TVar Kind Name          -- ^ Type variable
    | TCon Kind Name          -- ^ Type constructor
    | TArr a a                -- ^ Function type
    | TApp a a                -- ^ Type application
    | TGen i                  -- ^ Quantified type variable

-- | Type 
type TypeT i = Fix (TypeF i)

-- | Standalone type (a type that is not part of a type scheme)
type Type = TypeT Void

-- | A type which appears in a type scheme and therefore may contain quantified 
-- variables
type PolyType = TypeT Int

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Type class constraint
data PredicateT a = InClass Name a

-- | A standalone type class constraint
type Predicate = PredicateT Type

-- | A type class constraint which appears in a type scheme
type PolyPredicate = PredicateT Int

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Polymorphic type scheme
data Scheme = Forall [Kind] [PolyPredicate] PolyType

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Class of types that carry type information
class Typed a where
    typeOf :: a -> Type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- | Class of types that contain free type variables
class FreeIn t where
    free :: t -> [Name]

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

deriving instance (Show i, Show a) => 
    Show (TypeF i a)

deriving instance (Eq i, Eq a) => 
    Eq (TypeF i a)

deriving instance (Ord i, Ord a) => 
    Ord (TypeF i a)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

deriving instance Functor     (TypeF i)
deriving instance Foldable    (TypeF i)
deriving instance Traversable (TypeF i)

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
    free = (fst <$>) . typeVars

instance FreeIn Scheme where
    free (Forall _ _ t) = free t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Constructors
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Kind

kTyp :: Kind
kTyp = embed KTyp

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr

kClass :: Kind
kClass = embed KClass

kRow :: Kind
kRow = embed KRow

infixr 1 `kArr`

kFun :: Kind
kFun = kTyp `kArr` kTyp

kFun2 :: Kind
kFun2 = kTyp `kArr` kTyp `kArr` kTyp

-- Type

tVar :: Kind -> Name -> TypeT a
tVar = embed2 TVar

tGen :: Int -> PolyType
tGen = embed1 TGen

tCon :: Kind -> Name -> TypeT a
tCon = embed2 TCon

tArr :: TypeT a -> TypeT a -> TypeT a
tArr = embed2 TArr

infixr 1 `tArr`

tApp :: TypeT a -> TypeT a -> TypeT a
tApp = embed2 TApp

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
tList = tApp tListCon

-- Tuples

tTuple :: [TypeT a] -> TypeT a
tTuple types = foldl tApp (tCon kind (tupleCon (length types))) types
  where
    kind = foldr (const (kArr kTyp)) kTyp types

tPair :: TypeT a -> TypeT a -> TypeT a
tPair t1 t2 = tTuple [t1, t2]

tTriple :: TypeT a -> TypeT a -> TypeT a -> TypeT a
tTriple t1 t2 t3 = tTuple [t1, t2, t3]

-- Rows

tRowCon :: Name -> TypeT a
tRowCon label = tCon (kTyp `kArr` kRow `kArr` kRow) ("{" <> label <> "}")

tRowExtend :: Name -> TypeT a -> TypeT a -> TypeT a 
tRowExtend label ty = tApp (tApp (tRowCon label) ty) 

tEmptyRow :: TypeT a
tEmptyRow = tCon kRow "{}"

-- Records

tRecordCon :: TypeT a
tRecordCon = tCon (kArr kRow kTyp) "#Record" 

tRecord :: TypeT a -> TypeT a
tRecord = tApp tRecordCon

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

isVar :: Type -> Bool
isVar = project >>> \case
    TVar{} -> True
    _      -> False

isCon :: Type -> Bool
isCon = project >>> \case
    TCon{} -> True
    _      -> False

getTypeVar :: Type -> Maybe Name
getTypeVar = project >>> \case
    TVar _ var -> Just var
    _          -> Nothing

getTypeCon :: Type -> Maybe Name
getTypeCon = project >>> \case
    TCon _ con -> Just con
    _          -> Nothing

getTypeIndex :: PolyType -> Maybe Int
getTypeIndex = project >>> \case
    TGen i -> Just i
    _      -> Nothing

kindOf :: Type -> Kind
kindOf = para $ \case
    TApp (_, Fix (KArr _ k)) _ -> k
    TVar k _ -> k
    TCon k _ -> k
    TArr{}   -> kTyp

typeVars :: TypeT a -> [(Name, Kind)]
typeVars = nub . cata alg where
    alg = \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        _          -> []

upgrade :: TypeT a -> PolyType
upgrade = cata $ \case
    TVar k var -> tVar k var
    TCon k con -> tCon k con
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2

replaceBound :: [Type] -> PolyType -> Type
replaceBound ts = cata $ \case
    TGen n     -> ts !! n
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2
    TVar k var -> tVar k var
    TCon k con -> tCon k con

toScheme :: TypeT a -> Scheme
toScheme = Forall [] [] . upgrade

isRow :: Type -> Bool
isRow t = kRow == kindOf t

tupleCon :: Int -> Name
tupleCon size = "(" <> Text.replicate (pred size) "," <> ")"

predicateName :: PredicateT a -> Name
predicateName (InClass n _) = n

predicateType :: PredicateT a -> a
predicateType (InClass _ t) = t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

typeToRow :: Type -> Row Type
typeToRow t = Row m r 
  where
    (m, r) = flip para t $ \case
        TCon (Fix KRow) "{}" -> (mempty, Nothing)
        TVar (Fix KRow) var  -> (mempty , Just var)
        TApp (t1, _) (_, r)  -> first (insert t1) r
        _                    -> error "Not a row type"
    getLabel :: Type -> Name
    getLabel = cata $ \case
        TApp t1 _ -> t1
        TCon _ c  -> Text.tail (Text.init c)
        TVar _ v  -> ""

    insert t = 
        Map.insertWith (<>) (getLabel t) (case project t of TApp _ a -> [a])

rowToType :: Row Type -> Type
rowToType (Row map r) = Map.foldrWithKey (flip . foldr . tRowExtend) leaf map
  where
    leaf = case r of
      Nothing -> tEmptyRow
      Just v  -> tVar kRow v
