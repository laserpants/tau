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

isRow :: Type -> Bool
isRow t = kRow == kindOf t

unify :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
unify = undefined

match :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
match = undefined

unifyPairs :: (MonadError Error m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
unifyPairs = undefined

matchPairs :: (MonadError Error m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
matchPairs = undefined

unifyRowTypes :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
unifyRowTypes = undefined

matchRowTypes :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
matchRowTypes = undefined
