{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Unification where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Data.Function ((&))
import Tau.Compiler.Substitution
import Tau.Lang
import Tau.Tool
import Tau.Type
import qualified Data.Text as Text

type Error = String

bind :: (MonadError Error m) => Name -> Kind -> Type -> m TypeSubstitution
bind name kind ty
    | ty == tVar kind name                    = pure mempty
    | name `elem` free ty                     = throwError "Infinite type"
    | kind /= kindOf ty                       = throwError "Kind mismatch"
    | otherwise                               = pure (name `mapsTo` ty)

unify :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
unify t u
    | isRow t && isRow u                      = unifyRowTypes t u
    | otherwise                               = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _                     = bind name kind u
    fn _ (TVar kind name)                     = bind name kind t
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError "Cannot unify"

match :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
match t u
    | isRow t && isRow u                      = matchRowTypes t u
    | otherwise                               = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _                     = bind name kind u
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError "Cannot match"

unifyRowTypes :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
unifyRowTypes t u = fn (rowRep t) (rowRep u)
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn _ (RVar var)                           = bind var kRow t
    fn r s                                    = unifyRows (embed r) (embed s)

matchRowTypes :: (MonadError Error m) => Type -> Type -> m TypeSubstitution
matchRowTypes t u = fn (rowRep t) (rowRep u)
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn r s                                    = unifyRows (embed r) (embed s)

unifyPairs :: (MonadError Error m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

matchPairs :: (MonadError Error m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
matchPairs (t1, t2) (u1, u2) = do
    sub1 <- match t1 u1
    sub2 <- match t2 u2
    merge sub1 sub2 & maybe (throwError "Merge failed") pure

rowRep :: Type -> RowF Type (Row Type)
rowRep = project . unfoldRowType

unfoldRowType :: Type -> Row Type
unfoldRowType =
    para $ \case
        TCon (Fix KRow) "{}" -> rNil
        TVar (Fix KRow) var  -> rVar var
        TApp (t1, _) (_, b)  -> rExt (getLabel t1)
                                     (case project t1 of TApp _ a -> a) b
  where
    getLabel :: Type -> Name
    getLabel = cata $ \case
        TApp t1 _ -> t1
        TCon _ c  -> Text.tail (Text.init c)

unifyRows :: (MonadError String m) => Row Type -> Row Type -> m TypeSubstitution
unifyRows r s = 
    undefined
