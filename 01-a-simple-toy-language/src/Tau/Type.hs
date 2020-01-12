{-# LANGUAGE LambdaCase #-}
module Tau.Type where

import Data.Map (Map)
import Data.Set (Set, union, difference)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set


data Type
    = TyVar !Var
    | TyCon !Name
    | TyArr !Type !Type
    deriving (Show, Eq, Ord)


tyBool :: Type
tyBool = TyCon "Bool"


tyInt :: Type
tyInt = TyCon "Int"


class Free a where
    free :: a -> Set Var


instance Free a => Free [a] where
    free = foldr (union . free) Set.empty


instance Free Type where
    free (TyVar name)  = Set.singleton name
    free (TyArr t1 t2) = free t1 `union` free t2
    free _             = Set.empty


data Scheme = Forall !(Set Var) !Type
    deriving (Show, Eq)


instance Free Scheme where
    free (Forall vars tau) = free tau `difference` vars


-- | A substitution is a function from type variables to types.
--
type Sub = Map Var Type


substitute :: Var -> Type -> Sub
substitute = Map.singleton


emptySub :: Sub
emptySub = Map.empty


-- | Compose substitutions
--
compose :: Sub -> Sub -> Sub
compose sub1 sub2 =
    Map.map (apply sub1) sub2 `Map.union` sub1


class Substitutable a where
    apply :: Sub -> a -> a


instance Substitutable a => Substitutable [a] where
    apply = map . apply


-- | Apply a substitution to a type.
--
instance Substitutable Type where
    apply sub (TyVar name) =
        Map.findWithDefault (TyVar name) name sub

    apply sub (TyArr t1 t2) =
        TyArr (apply sub t1) (apply sub t2)

    apply _ tau = tau


data Constraint = Constraint !Type !Type
    deriving (Show, Eq)


instance Substitutable Constraint where
    apply sub (Constraint t1 t2) =
        Constraint (apply sub t1) (apply sub t2)
