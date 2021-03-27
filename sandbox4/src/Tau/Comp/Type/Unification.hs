{-# LANGUAGE FlexibleContexts #-}
module Tau.Comp.Type.Unification where

import Control.Monad.Except
import Data.Function ((&))
import Tau.Comp.Type.Substitution
import Tau.Lang.Type
import Tau.Lang.Type.Row
import Tau.Util (Fix(..), Name, project, embed)

bind :: (MonadError String m) => Name -> Kind -> Type -> m Substitution
bind name kind ty
    | ty == tVar kind name                    = pure mempty
    | name `elem` (fst <$> typeVars ty)       = throwError "InfiniteType"
    | Just kind /= kindOf ty                  = throwError "KindMismatch"
    | otherwise                               = pure (name `mapsTo` ty)

isRow :: Type -> Bool
isRow t = Just kRow == kindOf t

unify :: (MonadError String m) => Type -> Type -> m Substitution
unify t u 
    | isRow t && isRow u                      = unifyRowTypes t u
    | otherwise                               = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = unifyPairs (t1, t2) (u1, u2)
    fn (TVar kind name) _                     = bind name kind u
    fn _ (TVar kind name)                     = bind name kind t
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError "CannotUnify"

match :: (MonadError String m) => Type -> Type -> m Substitution
match t u = fn (project t) (project u) 
  where
    fn (TArr t1 t2) (TArr u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TApp t1 t2) (TApp u1 u2)              = matchPairs (t1, t2) (u1, u2)
    fn (TVar k name) _ | Just k == kindOf u   = pure (name `mapsTo` u)
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError "CannotMatch"

unifyPairs :: (MonadError String m) => (Type, Type) -> (Type, Type) -> m Substitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

matchPairs :: (MonadError String m) => (Type, Type) -> (Type, Type) -> m Substitution
matchPairs (t1, t2) (u1, u2) = do
    sub1 <- match t1 u1
    sub2 <- match t2 u2
    merge sub1 sub2 & maybe (throwError "MergeFailed") pure

unifyRowTypes :: (MonadError String m) => Type -> Type -> m Substitution
unifyRowTypes t u = fn (project (unfoldRow t)) (project (unfoldRow u))
  where
    fn RNil RNil                              = pure mempty
    fn (RVar var) _                           = bind var kRow u
    fn _ (RVar var)                           = bind var kRow t
    fn (RExt label t1 r1) s =
        case project <$> rowPermutation label (embed s) of
            Just (RExt _ t2 r2) -> do
                sub1 <- unify t1 t2
                unify (apply sub1 (foldRow r1)) (apply sub1 (foldRow r2))
            Nothing ->
                throwError "CannotUnfy"
    fn _ _                                    = throwError "CannotUnify"
