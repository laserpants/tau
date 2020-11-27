{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE StrictData       #-}
module Tau.Type.Solver where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Supply
import Data.List (nub, delete, find)
import Data.Set.Monad (Set, union, intersection, (\\))
import Tau.Type
import Tau.Type.Inference
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Data.Set.Monad as Set

isSolvable :: [Constraint] -> Constraint -> Bool
isSolvable cs (Implicit _ t2 (Monoset mono)) = Set.null vars where
    vars = free t2 \\ mono `intersection` active cs
isSolvable _ _ = True

choice :: [Constraint] -> Maybe ([Constraint], Constraint)
choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]

runUnify :: ExceptT UnificationError Infer a -> Infer a
runUnify m = runExceptT (withExceptT UnificationError m) >>= liftEither

solve :: [Constraint] -> Infer (Substitution, [TyClass])
solve = flip runStateT [] . solver
  where
    solver :: [Constraint] -> StateT [TyClass] Infer Substitution
    solver [] = pure mempty
    solver cs0 = do
        (cs, c) <- maybe (throwError CannotSolve) pure (choice cs0)
        case c of
            Equality t1 t2 -> do
                sub1 <- mapStateT runUnify (unify t1 t2)
                modify (apply sub1)
                sub2 <- solver (apply sub1 cs)
                pure (sub2 <> sub1)

            Implicit t1 t2 (Monoset vars) ->
                solver (Explicit t1 (generalize vars t2):cs)

            Explicit t1 scheme -> do
                (t2, ps1) <- instantiate scheme
                modify (<> ps1)
                solver (Equality t1 t2:cs)

generalize :: Set Name -> Type -> Scheme
generalize set ty = Forall ks (apply s qt) where
    qt = [] :=> ty
    (vs, ks) = unzip [(v, k) | (v, k) <- vars ty, v `Set.notMember` set]
    s = fromList (zip vs (tBound <$> [0..]))

vars :: Type -> [(Name, Kind)]
vars ty = nub . flip cata ty $ \case
    TVar k var -> [(var, k)]
    TArr t1 t2 -> t1 <> t2
    TApp t1 t2 -> t1 <> t2
    ty         -> mempty

instantiate :: (MonadSupply Name m) => Scheme -> m (Type, [TyClass])
instantiate (Forall ks s@(ps :=> t)) = do
    ts <- traverse freshVar ks
    pure (replaceBound ts t, instConstraint ts <$> ps)
  where
    freshVar k = tVar k <$> supply
    instConstraint ts (TyClass name ty) = TyClass name (replaceBound ts ty)

replaceBound :: [Type] -> Type -> Type 
replaceBound ts = cata $ \case
    TBound n   -> ts !! n
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2
    TVar k n   -> tVar k n 
    TCon k n   -> tCon k n 
