{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE StrictData           #-}
module Tau.Type.Substitution where

import Control.Arrow
import Control.Monad (join)
import Data.List (intersect, transpose)
import Data.Map.Strict (Map)
import Data.Set.Monad (Set, union)
import Tau.Expr
import Tau.Type
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

newtype Substitution = Subst { getSubst :: Map Name Type }
    deriving (Show, Eq)

domain :: Substitution -> [Name]
domain (Subst sub) = Map.keys sub

nullSubst :: Substitution
nullSubst = Subst mempty

fromList :: [(Name, Type)] -> Substitution
fromList = Subst . Map.fromList

mapsTo :: Name -> Type -> Substitution
mapsTo name val = Subst (Map.singleton name val)

substWithDefault :: Type -> Name -> Substitution -> Type
substWithDefault def name = Map.findWithDefault def name . getSubst

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = Subst (fmap (apply s1) (getSubst s2) `Map.union` getSubst s1)

merge :: Substitution -> Substitution -> Maybe Substitution
merge s1 s2 = 
    if all equal (domain s1 `intersect` domain s2)
        then Just (Subst (getSubst s1 `Map.union` getSubst s2))
        else Nothing
  where
    equal v = let app = (`apply` tVar kStar v) in app s1 == app s2

instance Semigroup Substitution where
    (<>) = compose

instance Monoid Substitution where
    mempty = nullSubst

class Substitutable t where
    apply :: Substitution -> t -> t

class Free t where
    free :: t -> Set Name

instance (Substitutable t) => Substitutable [t] where
    apply = fmap . apply

instance (Free t) => Free [t] where
    free = foldr (Set.union . free) mempty

instance Substitutable Type where
    apply sub = cata $ \case
         TVar kind var -> substWithDefault (tVar kind var) var sub
         TArr t1 t2    -> tArr t1 t2
         TApp t1 t2    -> tApp t1 t2
         ty            -> Fix ty

instance Free Type where
    free = cata $ \case
        TVar _ var -> Set.singleton var
        TArr t1 t2 -> t1 `union` t2
        TApp t1 t2 -> t1 `union` t2
        ty         -> mempty

instance Substitutable TypeClass where
    apply sub (TypeClass name t) = TypeClass name (apply sub t)

instance Free TypeClass where
    free (TypeClass _ ty) = free ty

instance (Substitutable t) => Substitutable (Qualified t) where
    apply = fmap . apply

instance (Free t) => Free (Qualified t) where
    free (ps :=> t) = free ps `union` free t

instance Substitutable Scheme where
    apply sub (Forall kinds qt) = Forall kinds (apply sub qt)

instance Free Scheme where
    free (Forall _ qt) = free qt

instance (Substitutable t) => Substitutable (Assumption t) where
    apply = fmap . apply 

instance (Free t) => Free (Assumption t) where
    free (_ :>: t) = free t

instance Substitutable (Expr Type p q) where
    apply sub = cata $ \case
        EVar t name        -> varExpr (apply sub t) name
        ECon t con exprs   -> conExpr (apply sub t) con exprs
        ELit t lit         -> litExpr (apply sub t) lit
        EApp t exprs       -> appExpr (apply sub t) exprs
        ELet t rep ex1 ex2 -> letExpr (apply sub t) rep ex1 ex2
        ELam t rep ex      -> lamExpr (apply sub t) rep ex
        EIf  t cond tr fl  -> ifExpr  (apply sub t) cond tr fl
        EMat t exs eqs     -> matExpr (apply sub t) exs eqs
        EOp  t op          -> opExpr  (apply sub t) op

instance Free (Expr Type p q) where
    free = free . getTag 

instance Free (Pattern t) where
    free = cata $ \case
        PVar _ name -> Set.singleton name
        PCon _ _ ps -> unions ps
        _           -> mempty

instance Free (SimpleRep t) where
    free (PVar _ name) = Set.singleton name 
    free (PCon _ _ ns) = Set.fromList ns
