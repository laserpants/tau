{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Type where
-- Tau.Lang.Type

import Control.Arrow (second)
import Control.Comonad.Cofree
import Control.Monad.Supply
import Data.Functor.Foldable
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Data.Void
import Tau.Env
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

-- | Base functor for Kind
data KindF a 
    = KTyp
--  | KCls
    | KArr a a
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

type Type = TypeT Void
type SchemeType = TypeT Int

-- | Type class constraints
data PredicateT a = InClass Name a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type Predicate = PredicateT Type 
type SchemePredicate = PredicateT Int

-- | Polymorphic type schemes
data Scheme = Forall [Kind] [SchemePredicate] SchemeType
    deriving (Show, Eq)

-- | Type class
type Class a = ([Name], [Instance a])

-- | Type class instance
data Instance a = Instance 
    { instancePredicates :: [Predicate] 
    , instanceType       :: Type 
    , instanceDict       :: a
    } deriving (Show, Eq)

class Free t where
    free :: t -> Set Name

instance (Free t) => Free [t] where
    free = foldr (Set.union . free) mempty

instance Free (TypeT a) where
    free = cata $ \case
        TVar _ var     -> Set.singleton var
        TArr t1 t2     -> t1 `Set.union` t2
        TApp t1 t2     -> t1 `Set.union` t2
        ty             -> mempty

instance Free (PredicateT (TypeT a)) where
    free (InClass _ ty) = free ty

instance Free Scheme where
    free (Forall _ _ ty) = free ty

class Typed a where
    typeOf :: a -> Type

instance Typed Type where
    typeOf = id

getTypeVar :: Type -> Maybe Name
getTypeVar = cata $ \case
    TVar _ v -> Just v
    _        -> Nothing

getTypeCon :: Type -> Maybe Name
getTypeCon = cata $ \case
    TCon _ c -> Just c
    _        -> Nothing

getTypeIndex :: SchemeType -> Maybe Int
getTypeIndex = cata $ \case
    TGen n -> Just n
    _      -> Nothing

toScheme :: Type -> Scheme
toScheme = Forall [] [] . upgrade

newTVar :: (MonadSupply Name m) => Kind -> m (TypeT a)
newTVar kind = tVar kind <$> supply 

recordConstructor :: [Name] -> TypeT a
recordConstructor names = 
    tCon kind ("{" <> Text.intercalate "," names <> "}")
  where 
    kind = foldr kArr kTyp (replicate (length names) kTyp)

upgrade :: Type -> SchemeType
upgrade = cata $ \case
    TVar k var -> tVar k var
    TCon k con -> tCon k con
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2

replaceBound :: [Type] -> SchemeType -> Type
replaceBound ts = cata $ \case
    TGen n     -> ts !! n
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2
    TVar k var -> tVar k var
    TCon k con -> tCon k con

kindOf :: Type -> Maybe Kind
kindOf = histo $ \case
    TApp (Just t :< _) _ -> appKind (project t) 
    TCon k _             -> Just k
    TVar k _             -> Just k
    TArr{}               -> Just kTyp
  where
    appKind (KArr _ k)    = Just k
    appKind _             = Nothing

kTyp :: Kind
kTyp = embed KTyp

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr 

infixr 1 `kArr`

kFun :: Kind
kFun = kTyp `kArr` kTyp

tVar :: Kind -> Name -> TypeT a
tVar = embed2 TVar 

tGen :: Int -> SchemeType
tGen = embed1 TGen 

tCon :: Kind -> Name -> TypeT a
tCon = embed2 TCon 

tArr :: TypeT a -> TypeT a -> TypeT a
tArr = embed2 TArr 

infixr 1 `tArr`

tApp :: TypeT a -> TypeT a -> TypeT a
tApp = embed2 TApp 

typ :: Name -> Type
typ = tCon kTyp

tUnit :: Type
tUnit = typ "Unit"

tBool :: Type
tBool = typ "Bool" 

tInt :: Type
tInt = typ "Int" 

tInteger :: Type
tInteger = typ "Integer"

tFloat :: Type
tFloat = typ "Float" 

tString :: Type
tString = typ "String" 

tChar :: Type
tChar = typ "Char" 

tListCon :: Type
tListCon = tCon kFun "List"

tList :: Type -> Type
tList = tApp tListCon 
