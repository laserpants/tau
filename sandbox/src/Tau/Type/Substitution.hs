{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE StrictData           #-}
-- {-# LANGUAGE TypeSynonymInstances #-}
module Tau.Type.Substitution where

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
    equal v = let app = (`apply` tvar star v) in app s1 == app s2

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
         TVar kind var -> substWithDefault (tvar kind var) var sub
         TArr t1 t2    -> tarr t1 t2
         TApp t1 t2    -> tapp t1 t2
         ty            -> Fix ty

instance Free Type where
    free = cata $ \case
        TVar _ var -> Set.singleton var
        TArr t1 t2 -> t1 `union` t2
        TApp t1 t2 -> t1 `union` t2
        ty         -> mempty

instance Substitutable TyClass where
    apply sub (TyClass name t) = TyClass name (apply sub t)

instance Free TyClass where
    free (TyClass _ ty) = free ty

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

instance Substitutable (Expr Type) where
    apply sub = cata $ \case
        EVar t name            -> tagVar (apply sub t) name
        ELit t lit             -> tagLit (apply sub t) lit
        EApp t exprs           -> tagApp (apply sub t) exprs
        ELet t pat expr1 expr2 -> tagLet (apply sub t) pat expr1 expr2
        ELam t pat expr1       -> tagLam (apply sub t) pat expr1

--instance Substitutable (Expr Type p) where
--    apply sub = cata $ \case
--        EVar t name            -> tagVar (apply sub t) name
--        ELit t lit             -> tagLit (apply sub t) lit
--        EApp t exprs           -> tagApp (apply sub t) exprs
--        ELet t pat expr1 expr2 -> tagLet (apply sub t) pat expr1 expr2
--        ELam t pat expr1       -> tagLam (apply sub t) pat expr1

instance Free (Expr Type) where
    free = cata $ \case
        EVar t name            -> free t
        ELit t lit             -> free t
        EApp t exprs           -> free t
        ELet t pat expr1 expr2 -> free t
        ELam t pat expr1       -> free t

--instance Free (Expr Type p) where
--    free = cata $ \case
--        EVar t name            -> free t
--        ELit t lit             -> free t
--        EApp t exprs           -> free t
--        ELet t pat expr1 expr2 -> free t
--        ELam t pat expr1       -> free t
