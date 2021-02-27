{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Lang.Type where

import Control.Arrow (second, (<<<), (>>>))
import Control.Comonad.Cofree
import Control.Monad.Supply
import Data.Functor.Foldable
import Data.List (nub)
import Data.Void
import Tau.Util
import qualified Data.Text as Text

-- | Base functor for Kind
data KindF a
    = KTyp                    -- ^ A concrete type (kind of value-types)
    | KArr a a                -- ^ Type constructor
    | KCls                    -- ^ A type class constraint
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

-- | Kinds
type Kind = Fix KindF

-- | Base functor for Type
data TypeF g a
    = TVar Kind Name
    | TCon Kind Name
    | TArr a a
    | TApp a a
    | TGen g
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

-- | Types
type TypeT a = Fix (TypeF a)

-- | Standalone type (a type that is not part of a type scheme)
type Type = TypeT Void

-- | A type which appears in a type scheme
type PolyType = TypeT Int

-- | Type class constraints
data PredicateT a = InClass Name a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | A standalone type-class constraint
type Predicate = PredicateT Type

-- | A type-class constraint which appears in a type scheme
type PolyPredicate = PredicateT Int

-- | Polymorphic type schemes
data Scheme = Forall [Kind] [PolyPredicate] PolyType
    deriving (Show, Eq)

-- | Type class
type Class a = ([Name], [Instance a])

-- | Type class instance
data Instance a = Instance
    { predicates   :: [Predicate]
    , instanceType :: Type
    , instanceDict :: a
    } deriving (Show, Eq)

class Typed a where
    typeOf :: a -> Type

instance Typed Type where
    typeOf = id

isVar :: Type -> Bool
isVar = project >>> \case
    TVar{}   -> True
    _        -> False

getTypeVar :: Type -> Maybe Name
getTypeVar = project >>> \case
    TVar _ v -> Just v
    _        -> Nothing

getTypeCon :: Type -> Maybe Name
getTypeCon = project >>> \case
    TCon _ c -> Just c
    _        -> Nothing

getTypeIndex :: PolyType -> Maybe Int
getTypeIndex = project >>> \case
    TGen n   -> Just n
    _        -> Nothing

toScheme :: Type -> Scheme
toScheme = Forall [] [] . upgrade

newTVar :: (MonadSupply Name m) => Kind -> m (TypeT a)
newTVar kind = tVar kind <$> supply

recordCon :: [Name] -> Name
recordCon names = "{" <> Text.intercalate "," names <> "}"

recordKeys :: Name -> [Name]
recordKeys tag = maybe [] (Text.split (== ',')) items
  where
    items = Text.stripPrefix "{" =<< Text.stripSuffix "}" tag

tupleCon :: Int -> Name
tupleCon size = "(" <> Text.replicate (pred size) "," <> ")"

upgrade :: Type -> PolyType
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

kindOf :: TypeT a -> Maybe Kind
kindOf = histo $ \case
    TApp (Just t :< _) _ -> appKind (project t)
    TCon k _             -> Just k
    TVar k _             -> Just k
    TArr{}               -> Just kTyp
  where
    appKind (KArr _ k) = Just k
    appKind _ = Nothing

class Free t where
    free :: t -> [Name]

instance (Free t) => Free [t] where
    free = concatMap free

instance Free (TypeT a) where
    free = (fst <$>) . typeVars

instance Free Scheme where
    free (Forall _ _ t) = free t

typeVars :: TypeT a -> [(Name, Kind)]
typeVars = nub . cata alg where
    alg = \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        _          -> []

kTyp :: Kind
kTyp = embed KTyp

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr

infixr 1 `kArr`

kFun :: Kind
kFun = kTyp `kArr` kTyp

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

tUnit :: TypeT a
tUnit = typ "Unit"

tBool :: TypeT a
tBool = typ "Bool"

tInt :: TypeT a
tInt = typ "Int"

tInteger :: TypeT a
tInteger = typ "Integer"

tFloat :: TypeT a
tFloat = typ "Float"

tString :: TypeT a
tString = typ "String"

tChar :: TypeT a
tChar = typ "Char"

tListCon :: TypeT a
tListCon = tCon kFun "List"

tList :: TypeT a -> TypeT a
tList = tApp tListCon

tRecord :: [Name] -> [TypeT a] -> TypeT a
tRecord names = foldl tApp (tCon kind (recordCon names))
  where
    kind = foldr kArr kTyp (replicate (length names) kTyp)

tTuple :: [TypeT a] -> TypeT a
tTuple types = foldl tApp (tCon kind (tupleCon (length types))) types
  where
    kind = foldr (const (kArr kTyp)) kTyp types

tPair :: TypeT a -> TypeT a -> TypeT a
tPair t1 t2 = tTuple [t1, t2]

tTriple :: TypeT a -> TypeT a -> TypeT a -> TypeT a
tTriple t1 t2 t3 = tTuple [t1, t2, t3]
