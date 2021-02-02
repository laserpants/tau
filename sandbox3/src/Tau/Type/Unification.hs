{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
module Tau.Type.Unification where

import Control.Monad.Except
import Data.Set.Monad (Set)
import Tau.Type
import Tau.Type.Main
import Tau.Type.Substitution
import Tau.Util
import qualified Data.Set.Monad as Set

free :: Type -> Set Name
free = cata $ \case
    TVar _ var -> Set.singleton var
    TArr t1 t2 -> t1 `Set.union` t2
    TApp t1 t2 -> t1 `Set.union` t2
    ty         -> mempty

bind :: (MonadError String m) => Name -> Kind -> Type -> m Substitution
bind name kind ty
    | ty == tVar kind name                    = pure mempty
    | name `elem` free ty                     = throwError "InfiniteType" -- throwError InfiniteType
    | Just kind /= kindOf ty                  = throwError "KindMismatch" -- throwError KindMismatch
    | otherwise                               = pure (name `mapsTo` ty)

unify :: (MonadError String m) => Type -> Type -> m Substitution
unify t u = fn (project t) (project u) where
    fn (TArr t1 t2) (TArr u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _                     = bind name kind u
    fn _ (TVar kind name)                     = bind name kind t
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError "CannotUnify" -- throwError CannotUnify

match :: (MonadError String m) => Type -> Type -> m Substitution
match t u = fn (project t) (project u) where
    fn (TArr t1 t2) (TArr u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TVar k name) _ | Just k == kindOf u   = pure (name `mapsTo` u)
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError "CannotMatch" -- throwError CannotMatch

unifyPairs :: (MonadError String m) => (Type, Type) -> (Type, Type) -> m Substitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

matchPairs :: (MonadError String m) => (Type, Type) -> (Type, Type) -> m Substitution
matchPairs (t1, t2) (u1, u2) = do
    sub1 <- match t1 u1
    sub2 <- match t2 u2
    case merge sub1 sub2 of
        Nothing  -> throwError "MergeFailed" -- throwError MergeFailed
        Just sub -> pure sub
