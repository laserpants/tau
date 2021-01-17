{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData       #-}
module Tau.Type.Unification where

import Control.Monad.Except (MonadError, throwError)
import Tau.Type
import Tau.Type.Substitution
import Tau.Util

bind :: (Monad m) => Name -> Kind -> Type -> m Substitution
bind name kind ty
    | ty == tVar kind name   = pure mempty
    | name `elem` free ty    = error "InfiniteType" -- throwError InfiniteType
    | Just kind /= kindOf ty = error "KindMismatch" -- throwError KindMismatch
    | otherwise              = pure (name `mapsTo` ty)

----bindP :: (Monoid c, Eq c, MonadError TypeError m) => Name -> Kind -> TypePlus c -> m (SubstitutionP c)
--bindP x name kind ty
--    | ty == tVarP x kind name   = pure mempty
----    | name `elem` free ty    = throwError InfiniteType
----    | Just kind /= kindOf ty = throwError KindMismatch
----    | otherwise              = pure (name `mapsTo` ty)
--

unify :: (Monad m) => Type -> Type -> m Substitution
unify t u = fn (project t) (project u) where
    fn (TArr t1 t2) (TArr u1 u2) = unifyPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2) = unifyPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _        = bind name kind u
    fn _ (TVar kind name)        = bind name kind t
    fn _ _ | t == u              = pure mempty
    fn _ _                       = error "CannotUnify" -- throwError CannotUnify

----unifyP :: (MonadError TypeError m) => TypePlus c -> TypePlus c -> m (SubstitutionP c)
--unifyP t u = fn (project t) (project u) where
--    fn (TArrP t1 t2) (TArrP u1 u2) = unifyPairsP (t1, t2) (u1, u2)
--    fn (TAppP t1 t2) (TAppP u1 u2) = unifyPairsP (t1, t2) (u1, u2)
--    fn (TVarP x kind name) _       = bindP x name kind u
--    --fn _ (TVar kind name)        = bind name kind t
--    --fn _ _ | t == u              = pure mempty
--    --fn _ _                       = throwError CannotUnify
--

unifyPairs :: (Monad m) => (Type, Type) -> (Type, Type) -> m Substitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

--unifyPairsP :: (MonadError TypeError m) => (TypePlus c, TypePlus c) -> (TypePlus c, TypePlus c) -> m (SubstitutionP c)
--unifyPairsP (t1, t2) (u1, u2) = do
--    undefined
----    sub1 <- unify t1 u1
----    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
----    pure (sub2 <> sub1)
--
--
--match :: (MonadError TypeError m) => Type -> Type -> m Substitution
--match t u = fn (project t) (project u) where
--    fn (TArr t1 t2) (TArr u1 u2)            = matchPairs (t1, t2) (u1, u2)
--    fn (TApp t1 t2) (TApp u1 u2)            = matchPairs (t1, t2) (u1, u2)
--    fn (TVar k name) _ | Just k == kindOf u = pure (name `mapsTo` u)
--    fn _ _ | t == u                         = pure mempty
--    fn _ _                                  = throwError CannotMatch
--
--matchPairs :: (MonadError TypeError m) => (Type, Type) -> (Type, Type) -> m Substitution
--matchPairs (t1, t2) (u1, u2) = do
--    sub1 <- match t1 u1
--    sub2 <- match t2 u2
--    case merge sub1 sub2 of
--        Nothing  -> throwError MergeFailed
--        Just sub -> pure sub
--
----unifyClass, matchClass :: (MonadError TypeError m) => TypeClass -> TypeClass -> m Substitution
----unifyClass = lift unify
----matchClass = lift match
--
----lift :: (MonadError TypeError m) => (Type -> Type -> m a) -> TypeClass -> TypeClass -> m a
----lift m (TypeClass c1 t1) (TypeClass c2 t2)
----    | c1 == c2  = m t1 t2
----    | otherwise = throwError ClassMismatch