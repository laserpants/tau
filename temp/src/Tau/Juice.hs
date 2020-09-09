{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Juice where

import Control.Monad.Except
import Control.Monad.State
import Data.Function (on)
import Data.Functor.Foldable
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
    apply sub = cata alg where
        alg :: Algebra TypeF Type
        alg (VarT var)    = substituteWithDefault (varT var) var sub
        alg (ArrT t1 t2)  = arrT t1 t2
        alg (AppT t1 t2)  = appT t1 t2
        alg ty            = Fix ty

instance Substitutable Type Scheme where
    apply sub (Forall vars tycls ty) =
        Forall vars (apply sub' <$> tycls) (apply sub' ty) where
        sub' = Substitution (foldr Map.delete (getSub sub) vars)

instance Substitutable Type TyClass where
    apply sub (TyCl name ty) = TyCl name (apply sub ty)

instance (Substitutable Type t) => Substitutable Name t where
    apply = apply . Substitution . fmap varT . getSub

instance Substitutable Kind Kind where
    apply sub = cata alg where
        alg :: Algebra KindF Kind
        alg (VarK name)  = substituteWithDefault (varK name) name sub
        alg (ArrK k1 k2) = arrK k1 k2
        alg StarK        = starK

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
    unify = run `on` unfix where
        run (ArrT t1 t2) (ArrT u1 u2) = unifyPair (t1, t2) (u1, u2)
        run (AppT t1 t2) (AppT u1 u2) = unifyPair (t1, t2) (u1, u2)
        run (VarT a) t                = bind varT a (Fix t)
        run t (VarT a)                = bind varT a (Fix t)
        run t u                       = unifyDefault (Fix t) (Fix u)

instance Unifiable Kind where
    unify = run `on` unfix where
        run (ArrK k1 k2) (ArrK l1 l2) = unifyPair (k1, k2) (l1, l2)
        run (VarK a) k                = bind varK a (Fix k)
        run k (VarK a)                = bind varK a (Fix k)
        run k l                       = unifyDefault (Fix k) (Fix l)

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
    free = cata alg where
        alg (VarT var)   = Set.singleton var
        alg (ArrT t1 t2) = t1 `union` t2
        alg (AppT t1 t2) = t1 `union` t2
        alg _            = mempty

instance Free TyClass where
    free (TyCl name ty) = free ty

instance Free Scheme where
    free (Forall vars _ ty) = free ty \\ Set.fromList vars

instance Free Kind where 
    free = cata alg where
        alg (ArrK k l)  = k `union` l
        alg (VarK name) = Set.singleton name
        alg _           = mempty

occursFreeIn :: (Free t) => Name -> t -> Bool
occursFreeIn var context = var `member` free context

-- ============================================================================
-- == Active
-- ============================================================================

class Active a where
    active :: a -> Set Name

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active
