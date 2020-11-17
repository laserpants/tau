{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData       #-}
module Tau.Type.Unification where

import Control.Monad.Except (MonadError, throwError)
import Tau.Type
import Tau.Type.Substitution
import Tau.Util

data UnificationError
    = CannotUnify
    | CannotMatch
    | InfiniteType
    | KindMismatch
    | MergeFailed
    | ClassMismatch
    | ContextReductionFailed
    deriving (Show, Eq)

bind :: (MonadError UnificationError m) => Name -> Kind -> Type -> m Substitution
bind name kind ty
    | ty == tvar kind name   = pure mempty
    | name `elem` free ty    = throwError InfiniteType
    | Just kind /= kindOf ty = throwError KindMismatch
    | otherwise              = pure (name `mapsTo` ty)

unify :: (MonadError UnificationError m) => Type -> Type -> m Substitution
unify t u = fn (unfix t) (unfix u) where
    fn (TArr t1 t2) (TArr u1 u2) = unifyPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2) = unifyPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _        = bind name kind u
    fn _ (TVar kind name)        = bind name kind t
    fn _ _ | t == u              = pure mempty
    fn _ _                       = throwError CannotUnify

unifyPairs :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m Substitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

match :: (MonadError UnificationError m) => Type -> Type -> m Substitution
match t u = fn (unfix t) (unfix u) where
    fn (TArr t1 t2) (TArr u1 u2)            = matchPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)            = matchPairs (t1, t2) (u1, u2)
    fn (TVar k name) _ | Just k == kindOf u = pure (name `mapsTo` u)
    fn _ _ | t == u                         = pure mempty
    fn _ _                                  = throwError CannotMatch

matchPairs :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m Substitution
matchPairs (t1, t2) (u1, u2) = do
    sub1 <- match t1 u1
    sub2 <- match t2 u2
    case merge sub1 sub2 of
        Nothing  -> throwError MergeFailed
        Just sub -> pure sub

unifyClass, matchClass :: (MonadError UnificationError m) => TyClass -> TyClass -> m Substitution
unifyClass = lift unify
matchClass = lift match

lift :: (MonadError UnificationError m) => (Type -> Type -> m a) -> TyClass -> TyClass -> m a
lift m (TyClass c1 t1) (TyClass c2 t2)
    | c1 == c2  = m t1 t2
    | otherwise = throwError ClassMismatch
