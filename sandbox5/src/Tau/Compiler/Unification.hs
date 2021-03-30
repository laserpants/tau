{-# LANGUAGE FlexibleContexts #-}
module Tau.Compiler.Unification where

import Control.Monad.Except
import Tau.Compiler.Substitution
import Tau.Tool
import Tau.Type

type Error = String

bind :: (MonadError Error m) => Name -> Kind -> Type -> m TypeSubstitution
bind name kind ty
    | ty == tVar kind name                    = pure mempty
    | name `elem` free ty                     = throwError "Infinite type"
    | kind /= kindOf ty                       = throwError "Kind mismatch"
    | otherwise                               = pure (name `mapsTo` ty)

unify :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
unify t u = undefined

match :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
match t u = undefined

unifyPairs :: (MonadError Error m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
unifyPairs (t1, t2) (u1, u2) = do
    undefined

matchPairs :: (MonadError Error m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
matchPairs (t1, t2) (u1, u2) = do
    undefined

unifyRowTypes :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
unifyRowTypes t u = 
    undefined

matchRowTypes :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
matchRowTypes t u = 
    undefined
