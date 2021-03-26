{-# LANGUAGE FlexibleContexts #-}
module Tau.Comp.Type.Unification where

import Control.Monad.Except
import Data.Function ((&))
import Tau.Comp.Type.Substitution
import Tau.Lang.Type
import Tau.Util (Fix(..), Name, project)

bind :: (MonadError String m) => Name -> Kind -> Type -> m Substitution
bind name kind ty
    | ty == tVar kind name                    = pure mempty
    | name `elem` (fst <$> typeVars ty)       = throwError "InfiniteType"
    | Just kind /= kindOf ty                  = throwError "KindMismatch"
    | otherwise                               = pure (name `mapsTo` ty)

unify :: (MonadError String m) => Type -> Type -> m Substitution
unify t u = fn (project t) (project u) 
  where
--    fn (TRow r) (TRow s)                      = unifyRows r s
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

--unifyRows :: (Eq g, MonadError String m) => RowT g -> RowT g -> m Substitution
--unifyRows r s = fn (project r) -- (project s)
--  where
--    fn (RExt label t1 r1)  
--        | r == s = pure mempty
--        | otherwise = case rowPermutation label s of
--            Just (Fix (RExt _ t2 r2)) ->
--                undefined
--            _ -> 
--                throwError "CannotMatch"
--    fn _ = 
--        throwError "CannotMatch"
