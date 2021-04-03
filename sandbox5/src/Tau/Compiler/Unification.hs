{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Unification where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Data.Function ((&))
import Data.Map.Strict (Map)
import Tau.Compiler.Error
import Tau.Compiler.Substitution
import Tau.Lang
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

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
unifyRowTypes t u = fn (asRow t) (asRow u)
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn _ (RVar var)                           = bind var kRow t
    fn r s                                    = unifyRows (embed r) (embed s)

matchRowTypes :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
matchRowTypes t u = fn (asRow t) (asRow u)
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn r s                                    = matchRows (embed r) (embed s)

asRow :: Type -> RowF Type (Row Type)
asRow = project . typeToRow

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
unifyRows r s = do
    (t1, t2, t3, t4) <- rowInfo r s
    sub1 <- unify t1 t2
    sub2 <- unify (apply sub1 t3) (apply sub1 t4)
    pure (sub2 <> sub1)

matchRows :: (MonadError UnificationError m) => Row Type -> Row Type -> m TypeSubstitution
matchRows r s = do
    (t1, t2, t3, t4) <- rowInfo r s
    sub1 <- match t1 t2
    sub2 <- match t3 t4
    merge sub1 sub2 & maybe (throwError MergeFailed) pure

rowInfo :: (MonadError UnificationError m) => Row Type -> Row Type -> m (Type, Type, Type, Type)
rowInfo r s =
    case rows of
        Nothing -> throwError IncompatibleRows
        Just (RExt _ t1 r1, RExt _ t2 r2) -> 
            pure (t1, t2, rowToType r1, rowToType r2)
  where
    rows = msum $ do
        r1@(RExt label _ _) <- project <$> rowSet r
        case project <$> rowPermutation s label of
            Nothing -> [Nothing]
            Just r2 -> [Just (r1, r2)]
