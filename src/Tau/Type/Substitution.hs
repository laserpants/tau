module Tau.Type.Substitution where

import Data.Map.Strict (Map)
import Tau.Core
import Tau.Type
import qualified Data.Map.Strict as Map

type Substitution = Map Name Type

compose :: Substitution -> Substitution -> Substitution
compose sub1 sub2 = Map.union (Map.map (apply sub1) sub2) sub1

empty :: Substitution
empty = Map.empty

singleton :: Name -> Type -> Substitution
singleton = Map.singleton

class Substitutable a where
    apply :: Substitution -> a -> a

instance Substitutable a => Substitutable [a] where
    apply = fmap . apply

instance Substitutable Type where
    apply sub (TVar var)   = Map.findWithDefault (TVar var) var sub
    apply sub (TArr t1 t2) = TArr (apply sub t1) (apply sub t2)
    apply sub (TApp t1 t2) = TApp (apply sub t1) (apply sub t2)
    apply _ ty = ty

instance Substitutable Scheme where
    apply sub (Forall vars ty) =
        Forall vars (apply (foldr Map.delete sub vars) ty)
