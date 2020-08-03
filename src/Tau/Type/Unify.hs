{-# LANGUAGE FlexibleContexts #-}
module Tau.Type.Unify 
    ( unify
    ) where

import Control.Monad.Except (MonadError, throwError)
import Data.Set.Monad (member)
import Tau.Core
import Tau.Type
import Tau.Type.Infer.Monad
import Tau.Type.Substitution (Substitution, apply, compose, singleton)

occursIn :: Name -> Type -> Bool
occursIn var ty = var `member` free ty

bind :: MonadError InferError m => Name -> Type -> m Substitution
bind var ty
    | TVar var == ty    = pure mempty
    | var `occursIn` ty = throwError InfiniteType
    | otherwise         = pure (singleton var ty)

unifyPair :: MonadError InferError m => (Type, Type) -> (Type, Type) -> m Substitution
unifyPair (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 `compose` sub1)

unify :: MonadError InferError m => Type -> Type -> m Substitution
unify (TArr t1 t2) (TArr u1 u2) = unifyPair (t1, t2) (u1, u2)
unify (TApp t1 t2) (TApp u1 u2) = unifyPair (t1, t2) (u1, u2)
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify t u
    | t == u    = pure mempty 
    | otherwise = throwError CannotUnify
