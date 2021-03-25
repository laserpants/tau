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
import Data.List (nub, sortOn)
import Data.Set.Monad (Set)
import Data.Void
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

-- | Base functor for Kind
data KindF a
    = KTyp                    -- ^ Kind of concrete (value) types
    | KArr a a                -- ^ Kind of type constructors
--  | KClc                    -- ^ Kind of type class constraints
--  | KRow 
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

-- | Kinds
type Kind = Fix KindF

-- | Base functor for Type
--data TypeF r g a 
--data TypeF r g a 
data TypeF g a 
    = TVar Kind Name
    | TCon Kind Name
    | TArr a a
    | TApp a a
--    | TRow r
    | TGen g
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

data RowF t a = RNil | RExt t a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''RowF
deriveEq1   ''RowF
deriveOrd1  ''RowF

-- | Row type
type Row t = Fix (RowF t)

-- | Types
--type TypeT g = Fix (TypeF Row g)
--type TypeT t g = Fix (TypeF t g)
type TypeT g = Fix (TypeF g)

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

predicateName :: PredicateT a -> Name
predicateName (InClass n _) = n

predicateType :: PredicateT a -> a
predicateType (InClass _ t) = t

class Typed a where
    typeOf :: a -> Type

instance Typed Type where
    typeOf = id

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

tupleCon :: Int -> Name
tupleCon size = "(" <> Text.replicate (pred size) "," <> ")"

maybeSplit :: Maybe Name -> [Name]
maybeSplit = maybe [] $ Text.split (== ',')

recordFieldNames :: Name -> [Name]
recordFieldNames tag = 
    maybeSplit (Text.stripPrefix "{" 
        =<< Text.stripSuffix "}" tag)

tupleElems :: Name -> [Name]
tupleElems tag = 
    maybeSplit (Text.stripPrefix "(" 
        =<< Text.stripSuffix ")" tag)

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

type TypeEnv = Env Scheme

instance Free TypeEnv where
    free = free . Env.elems

type Context = Env (Set Name)

kTyp :: Kind
kTyp = embed KTyp

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr

--kCls :: Kind
--kCls = embed KCls

infixr 1 `kArr`

kFun :: Kind
kFun = kTyp `kArr` kTyp

kFun2 :: Kind
kFun2 = kTyp `kArr` kTyp `kArr` kTyp

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

tVoid :: TypeT a
tVoid = typ "Void"

tUnit :: TypeT a
tUnit = typ "Unit"

tBool :: TypeT a
tBool = typ "Bool"

tInt :: TypeT a
tInt = typ "Int"

tInteger :: TypeT a
tInteger = typ "Integer"

--tNat :: TypeT a
--tNat = typ "Nat"

tFloat :: TypeT a
tFloat = typ "Float"

tDouble :: TypeT a
tDouble = typ "Double"

tString :: TypeT a
tString = typ "String"

tChar :: TypeT a
tChar = typ "Char"

tListCon :: TypeT a
tListCon = tCon kFun "List"

tList :: TypeT a -> TypeT a
tList = tApp tListCon

tRecord :: [(Name, TypeT a)] -> TypeT a
tRecord pairs = foldl tApp (tCon kind (recordCon ns)) ts
  where
    (ns, ts) = unzip (sortOn fst pairs)
    kind = foldr kArr kTyp (replicate (length pairs) kTyp)

tTuple :: [TypeT a] -> TypeT a
tTuple types = foldl tApp (tCon kind (tupleCon (length types))) types
  where
    kind = foldr (const (kArr kTyp)) kTyp types

tPair :: TypeT a -> TypeT a -> TypeT a
tPair t1 t2 = tTuple [t1, t2]

tTriple :: TypeT a -> TypeT a -> TypeT a -> TypeT a
tTriple t1 t2 t3 = tTuple [t1, t2, t3]
