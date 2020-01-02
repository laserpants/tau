{-# LANGUAGE LambdaCase #-}
module Tau.Type where

import Data.Map (Map)
import Data.Set (Set, union, difference)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set


data Type
    = TVar !Var
    | TInt
    | TBool
    | TArr !Type !Type
    deriving (Show, Eq, Ord)


class Free a where
    free :: a -> Set Var


instance Free a => Free [a] where
    free = foldr (union . free) Set.empty


instance Free Type where
    free (TVar name)  = Set.singleton name
    free (TArr t1 t2) = free t1 `union` free t2
    free _            = Set.empty


data Scheme = Forall !(Set Var) !Type
    deriving (Show, Eq)


instance Free Scheme where
    free (Forall vars tau) = free tau `difference` vars


type Sub = Map Var Type


substitute :: Sub -> Type -> Type
substitute sub = \case 
    TVar name ->
        Map.findWithDefault (TVar name) name sub

    TArr t1 t2 ->
        TArr (substitute sub t1) (substitute sub t2)

    tau ->
        tau


singleSub :: Var -> Type -> Sub
singleSub = Map.singleton


compose :: Sub -> Sub -> Sub
compose sub1 sub2 = 
    Map.map (substitute sub1) sub2 `Map.union` sub1
