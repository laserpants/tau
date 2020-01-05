{-# LANGUAGE LambdaCase #-}
module Tau.Type where

import Data.Map (Map)
import Data.Set (Set, union, difference)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set


data Type
    = TyVar !Var
    | TyInt
    | TyBool
    -- | TyCon !Var
    | TyArr !Type !Type
    deriving (Show, Eq, Ord)


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


sub :: Var -> Type -> Sub
sub = Map.singleton


emptySub :: Sub
emptySub = Map.empty


-- | Compose substitutions  
--
compose :: Sub -> Sub -> Sub
compose sub1 sub2 = 
    Map.map (substitute sub1) sub2 `Map.union` sub1


class Substitutable a where
    substitute :: Sub -> a -> a


instance Substitutable a => Substitutable [a] where
    substitute = map . substitute


-- | Apply a substitution to a type.
--
instance Substitutable Type where
    substitute sub (TyVar name) =
        Map.findWithDefault (TyVar name) name sub

    substitute sub (TyArr t1 t2) =
        TyArr (substitute sub t1) (substitute sub t2)

    substitute _ tau = tau


data Constraint = Constraint !Type !Type
    deriving (Show, Eq)


instance Substitutable Constraint where
    substitute sub (Constraint t1 t2) =
        Constraint (substitute sub t1) (substitute sub t2)
