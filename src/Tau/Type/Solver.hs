{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData       #-}
module Tau.Type.Solver where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Supply
import Data.List (find, delete)
import Data.Set.Monad (Set, union, intersection, (\\))
import Tau.Core
import Tau.Type
import Tau.Type.Infer.Monad
import Tau.Type.Substitution
import Tau.Type.Unify
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

type Assumption = (Name, Type)

removeAssumption :: Name -> [Assumption] -> [Assumption]
removeAssumption var = filter (\a -> fst a /= var)

removeMany :: [Name] -> [Assumption] -> [Assumption]
removeMany = flip (foldr removeAssumption)

data Constraint
    = Equality Type Type
    | Implicit Type Type Monoset
    | Explicit Type Scheme
    deriving (Show, Eq)

instance Substitutable Constraint where
    apply sub (Equality t1 t2)      = Equality (apply sub t1) (apply sub t2)
    apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
    apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)

class Active a where
    active :: a -> Set Name

instance Active Constraint where
    active (Equality t1 t2)      = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

instance Active a => Active [a] where
    active = join . Set.fromList . fmap active

isSolvable :: (Constraint, [Constraint]) -> Bool
isSolvable (Equality{}, _) = True
isSolvable (Explicit{}, _) = True
isSolvable (Implicit _ t2 (Monoset vars), cs) =
    Set.null (free t2 \\ vars `intersection` active cs)

choice :: [Constraint] -> Maybe (Constraint, [Constraint])
choice xs = find isSolvable [(x, ys) | x <- xs, let ys = delete x xs]

solve
    :: (MonadError InferError m, MonadSupply Type m)
    => [Constraint]
    -> m Substitution
solve [] = pure empty
solve xs =
    maybe (throwError CannotSolve) pure (choice xs)
        >>= uncurry (flip run)
  where
    run cs = \case
        Equality t1 t2 -> do
            sub1 <- unify t1 t2
            sub2 <- solve (apply sub1 cs)
            pure (sub2 `compose` sub1)

        Implicit t1 t2 (Monoset vars) ->
            solve (Explicit t1 (generalize vars t2):cs)

        Explicit t1 scheme -> do
            t2 <- instantiate scheme
            solve (Equality t1 t2:cs)

generalize :: Set Name -> Type -> Scheme
generalize vars ty = Forall (Set.toList (free ty \\ vars)) ty

instantiate :: (MonadSupply Type m) => Scheme -> m Type
instantiate (Forall vars0 ty) = do
    vars1 <- traverse (const supply) vars0
    let sub = Map.fromList (zip vars0 vars1)
    pure (apply sub ty)
