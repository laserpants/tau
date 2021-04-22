{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Unification where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List (intersect)
import Data.Map.Strict (Map, (!))
import Tau.Compiler.Error
import Tau.Compiler.Substitution hiding (null)
import Tau.Lang
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

data RowType a
    = RNil 
    | RVar a
    | RExt
    deriving (Show, Eq)

rowType :: Row Type -> RowType Name
rowType (Row m Nothing)  | null m = RNil
rowType (Row m (Just r)) | null m = RVar (unsafeGetTypeVar r)
rowType _                         = RExt

bind :: (MonadError UnificationError m) => Name -> Kind -> Type -> m TypeSubstitution
bind name kind ty
    | ty == tVar kind name                    = pure mempty
    | name `elem` free ty                     = throwError InfiniteType
    | kind /= kindOf ty                       = throwError KindMismatch
    | otherwise                               = pure (name `mapsTo` ty)

unify :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
unify t u
    | isRow t && isRow u                      = unifyRowTypes t u
    | otherwise                               = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _                     = bind name kind u
    fn _ (TVar kind name)                     = bind name kind t
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError IncompatibleTypes

match :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
match t u
    | isRow t && isRow u                      = matchRowTypes t u
    | otherwise                               = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _                     = bind name kind u
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError IncompatibleTypes

unifyRowTypes :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
unifyRowTypes t u = fn (rowType r) (rowType s)
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn _ (RVar var)                           = bind var kRow t
    fn _ _                                    = unifyRows r s
    r                                         = typeToRow t
    s                                         = typeToRow u

matchRowTypes :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
matchRowTypes t u = fn (rowType r) (rowType s)
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn _ _                                    = matchRows r s
    r                                         = typeToRow t
    s                                         = typeToRow u

unifyPairs :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

matchPairs :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
matchPairs (t1, t2) (u1, u2) = do
    sub1 <- match t1 u1
    sub2 <- match t2 u2
    merge sub1 sub2 & maybe (throwError MergeFailed) pure

unifyRows :: (MonadError UnificationError m) => Row Type -> Row Type -> m TypeSubstitution
unifyRows (Row m1 Nothing) (Row m2 Nothing)
    | Map.null m1 && Map.null m2              = pure mempty
unifyRows (Row m (Just r)) row | Map.null m   = bind (unsafeGetTypeVar r) kRow (rowToTag row)
unifyRows row (Row m (Just r)) | Map.null m   = bind (unsafeGetTypeVar r) kRow (rowToTag row)
unifyRows r1 r2 = do
    (sub1, sub2) <- rowSubs unifyRows unifyWith r1 r2
    pure (sub2 <> sub1)
  where
    unifyWith (t, u) sub = unify (apply sub t) (apply sub u)

matchRows :: (MonadError UnificationError m) => Row Type -> Row Type -> m TypeSubstitution
matchRows (Row m1 Nothing) (Row m2 Nothing)
    | Map.null m1 && Map.null m2              = pure mempty
matchRows (Row m (Just r)) row | Map.null m   = bind (unsafeGetTypeVar r) kRow (rowToTag row)
matchRows r1 r2 = do
    (sub1, sub2) <- rowSubs matchRows matchWith r1 r2
    merge sub1 sub2 & maybe (throwError MergeFailed) pure
  where
    matchWith (t, u) sub1 = do
        sub2 <- match t u
        merge sub1 sub2 & maybe (throwError MergeFailed) pure

rowSubs
  :: (MonadError UnificationError m)
  => (Row Type -> Row Type -> m TypeSubstitution)
  -> ((Type, Type) -> TypeSubstitution -> m TypeSubstitution)
  -> Row Type
  -> Row Type
  -> m (TypeSubstitution, TypeSubstitution)
rowSubs combineRows unifyFun (Row m1 r1) (Row m2 r2)
    | null mutualKeys = throwError IncompatibleRows
    | otherwise = do
        sub1 <- combineRows (Row (unique m1) r1) (Row (unique m2) r2)
        sub2 <- foldrM combine sub1 mutualKeys
        pure (sub1, sub2)
  where
    mutualKeys    = Map.keys m1 `intersect` Map.keys m2
    unique        = Map.filterWithKey (\k -> const (k `notElem` mutualKeys))
    combine k sub = foldrM unifyFun sub (zip (m1 ! k) (m2 ! k))
