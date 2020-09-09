{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Juice where

import Control.Monad.Except
import Control.Monad.State
import Data.Map.Strict (Map)
import Data.Set.Monad (Set, union, member, (\\))
import Tau.Type
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

-- ============================================================================
-- == Substitutable
-- ============================================================================

newtype Substitution a = Substitution { getSub :: Map Name a }
    deriving (Show, Eq)

class Substitutable s t where
    apply :: Substitution s -> t -> t

fromList :: [(Name, a)] -> Substitution a
fromList = Substitution . Map.fromList

compose 
  :: (Substitutable a a) 
  => Substitution a 
  -> Substitution a 
  -> Substitution a
compose sub1 sub2 = Substitution sub where
    sub = Map.map (apply sub1) (getSub sub2) `Map.union` getSub sub1

mapsTo :: Name -> a -> Substitution a
mapsTo name = Substitution . Map.singleton name

substituteWithDefault :: a -> Name -> Substitution a -> a
substituteWithDefault def name = Map.findWithDefault def name . getSub

instance Substitutable Type Type where
    apply sub ty@(VarT var) = substituteWithDefault ty var sub
    apply sub (ArrT t1 t2)  = ArrT (apply sub t1) (apply sub t2)
    apply sub (AppT t1 t2)  = AppT (apply sub t1) (apply sub t2)
    apply _ ty              = ty

instance Substitutable Type Scheme where
    apply sub (Forall vars tycls ty) =
        Forall vars (apply sub' <$> tycls) (apply sub' ty) where
        sub' = Substitution (foldr Map.delete (getSub sub) vars)

instance Substitutable Type TyClass where
    apply sub (TyCl name ty) = TyCl name (apply sub ty)

instance (Substitutable Type t) => Substitutable Name t where
    apply = apply . Substitution . fmap VarT . getSub

instance Substitutable Kind Kind where
    apply sub (VarK name)  = substituteWithDefault (VarK name) name sub
    apply sub (ArrK k1 k2) = ArrK (apply sub k1) (apply sub k2)
    apply _ StarK          = StarK

instance (Substitutable t t) => Semigroup (Substitution t) where
    (<>) = compose

instance (Substitutable t t) => Monoid (Substitution t) where
    mempty = Substitution mempty

-- ============================================================================
-- == Unifiable
-- ============================================================================

data UnificationError
    = CannotUnify
    | InfiniteType
    deriving (Show, Eq)

class Unifiable t where
    unify :: t -> t -> Either UnificationError (Substitution t)

instance Unifiable Type where
    unify (ArrT t1 t2) (ArrT u1 u2) = unifyPair (t1, t2) (u1, u2)
    unify (AppT t1 t2) (AppT u1 u2) = unifyPair (t1, t2) (u1, u2)
    unify (VarT a) t                = bind VarT a t
    unify t (VarT a)                = bind VarT a t
    unify t u                       = unifyDefault t u

instance Unifiable Kind where
    unify (ArrK k1 k2) (ArrK l1 l2) = unifyPair (k1, k2) (l1, l2)
    unify (VarK a) k                = bind VarK a k
    unify k (VarK a)                = bind VarK a k
    unify k l                       = unifyDefault k l

unifyPair 
  :: (Unifiable t, Substitutable t t) 
  => (t, t) 
  -> (t, t) 
  -> Either UnificationError (Substitution t)
unifyPair (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

bind 
  :: (Eq a, Free a) 
  => (Name -> a) 
  -> Name 
  -> a 
  -> Either UnificationError (Substitution a)
bind con var ty
    | con var == ty         = pure (Substitution mempty)
    | var `occursFreeIn` ty = throwError InfiniteType
    | otherwise             = pure (var `mapsTo` ty)

unifyDefault :: (Eq a) => a -> a -> Either UnificationError (Substitution a)
unifyDefault t u 
    | t == u    = pure (Substitution mempty)
    | otherwise = throwError CannotUnify

-- ============================================================================
-- == Free
-- ============================================================================

class Free t where
    free :: t -> Set Name

instance (Free t) => Free [t] where
    free = foldr (union . free) mempty

instance Free Type where
    free (VarT var)   = Set.singleton var
    free (ArrT t1 t2) = free t1 `union` free t2
    free (AppT t1 t2) = free t1 `union` free t2
    free _            = mempty

instance Free TyClass where
    free (TyCl name ty) = free ty

instance Free Scheme where
    free (Forall vars _ ty) = free ty \\ Set.fromList vars

instance Free Kind where
    free (ArrK k l)  = free k `union` free l
    free (VarK name) = Set.singleton name
    free _           = mempty

occursFreeIn :: (Free t) => Name -> t -> Bool
occursFreeIn var context = var `member` free context

-- ============================================================================
-- == Active
-- ============================================================================

class Active a where
    active :: a -> Set Name

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active
