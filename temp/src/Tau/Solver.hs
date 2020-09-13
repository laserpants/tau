{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
module Tau.Solver where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Supply
import Data.List (find, delete)
import Data.Set.Monad (Set, union, intersection, (\\))
import Data.Tuple.Extra (both)
import Tau.Type
import Tau.Util
import qualified Data.Set.Monad as Set

-- ============================================================================
-- == Type Constraints Solver
-- ============================================================================

-- | Monomorphic set
newtype Monoset = Monoset { getMonoset :: Set Name }
    deriving (Show, Eq)

insertIntoMonoset :: Name -> Monoset -> Monoset
insertIntoMonoset var (Monoset set) = Monoset (Set.insert var set)

insertManyIntoMonoset :: [Name] -> Monoset -> Monoset
insertManyIntoMonoset = flip (foldr insertIntoMonoset)

instance Free Monoset where
    free (Monoset set) = set

instance Substitutable Type Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . varT =<< set)

data TypeConstraint
    = Equality Type Type
    | Implicit Type Type Monoset
    | Explicit Type Scheme
    deriving (Show, Eq)

instance Substitutable Type TypeConstraint where
    apply sub (Equality t1 t2)      = Equality (apply sub t1) (apply sub t2)
    apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
    apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)

instance Active TypeConstraint where
    active (Equality t1 t2)      = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

isSolvable :: [TypeConstraint] -> TypeConstraint -> Bool
isSolvable cs (Implicit _ t2 (Monoset mono)) = Set.null vars where
    vars = free t2 \\ mono `intersection` active cs
isSolvable _ _ = True

choice :: [TypeConstraint] -> Maybe ([TypeConstraint], TypeConstraint)
choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]

solveTypes
  :: (MonadError UnificationError m, MonadSupply Name m)
  => [TypeConstraint]
  -> m (Substitution Type, [TyClass])
solveTypes = flip runStateT [] . solver

solver
  :: ( MonadState [TyClass] m
     , MonadError UnificationError m
     , MonadSupply Name m )
  => [TypeConstraint] 
  -> m (Substitution Type)
solver [] = pure (Substitution mempty)
solver constraints = do
    (cs, c) <- maybe (error "Unsolvable constraints") pure (choice constraints)
    case c of
        Equality t1 t2 -> do
            sub1 <- liftEither (unify t1 t2)
            modify (apply sub1 <$>)
            sub2 <- solver (apply sub1 <$> cs)
            modify (apply sub2 <$>)
            pure (sub2 <> sub1)

        Implicit t1 t2 (Monoset vars) -> do
            tycls <- get
            solver (Explicit t1 (generalize vars tycls t2):cs)

        Explicit t1 scheme -> do
            (t2, tycls) <- instantiate scheme
            modify (tycls <>)
            solver (Equality t1 t2:cs)

generalize :: Set Name -> [TyClass] -> Type -> Scheme
generalize vars tycls ty = Forall vars' (filter (inSet . free) tycls) ty where
    vars' = Set.toList (free ty \\ vars)
    inSet freeSet = or [v `elem` freeSet | v <- vars']

instantiate :: (MonadSupply Name m) => Scheme -> m (Type, [TyClass])
instantiate (Forall vars tycls ty) = do
    sub <- subFromList <$> (zip <$> pure vars <*> traverse (const supply) vars)
    pure (apply sub ty, apply sub <$> tycls)

-- ============================================================================
-- == Kind Constraints Solver
-- ============================================================================

type KindConstraint = (Kind, Kind)

solveKinds
  :: (MonadError UnificationError m)
  => [KindConstraint]
  -> m (Substitution Kind)
solveKinds [] = pure mempty
solveKinds ((k1, k2):cs) = do
    sub1 <- liftEither (unify k1 k2)
    sub2 <- solveKinds (both (apply sub1) <$> cs)
    pure (sub2 <> sub1)
