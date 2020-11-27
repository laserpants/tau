-- {-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Type.Inference where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Supply
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set, union, intersection, (\\))
import Tau.Expr
import Tau.Type
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Data.Set.Monad as Set

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

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active

instance Active Constraint where
    active (Equality t1 t2)      = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `Set.intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

newtype Monoset = Monoset { getMonoset :: Set Name }
    deriving (Show, Eq)

instance Substitutable Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . tVar kStar =<< set)

instance Free Monoset where
    free (Monoset set) = set

monosetInsert :: Name -> Monoset -> Monoset
monosetInsert var (Monoset set) = Monoset (Set.insert var set)

monosetInsertSet :: [Name] -> Monoset -> Monoset
monosetInsertSet = flip (foldr monosetInsert)

type TypeAssumption = Assumption Type

data InferError 
    = CannotSolve
    | UnificationError UnificationError
    | ImplementationError
    deriving (Show, Eq)

newtype Infer a = Infer { unInfer :: ExceptT InferError (ReaderT Monoset (Supply Name)) a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadSupply Name
    , MonadReader Monoset 
    , MonadError InferError )

runInfer :: Infer a -> Either InferError a
runInfer = unInfer
    >>> runExceptT
    >>> flip runReaderT (Monoset mempty) 
    >>> flip evalSupply (fmap (\n -> "a" <> show n) [1..])
    >>> fromMaybe (throwError ImplementationError)

--infer :: Expr t p -> Infer (Expr Type p, [TypeAssumption], [Constraint])
infer :: RepExpr t -> Infer (RepExpr Type, [TypeAssumption], [Constraint])
infer = cata $ \case
    EVar _ var -> do
        name <- supply
        let t = tVar kStar name 
        pure (tagVar t var, [var :>: t], [])

    ELit _ LUnit{}   -> pure (tagLit tUnit LUnit, [], [])
    ELit _ (LBool b) -> pure (tagLit tBool (LBool b), [], [])
    ELit _ (LInt n)  -> pure (tagLit tInt (LInt n), [], [])

    EApp _ exprs -> 
        foldl1 inferApp exprs

    ELet _ pat expr1 expr2 -> do
        (t0, ts) <- inferRep pat
        (t1, as1, cs1) <- expr1
        (t2, as2, cs2) <- expr2
        let cs3 = [Equality s t | v :>: s <- ts, w :>: t <- as1 <> as2, v == w]
        set <- ask
        pure ( tagLet (getTag t2) (setRepType t0 pat) t1 t2
             , removeAssumptionSet ts as1 <> removeAssumptionSet ts as2
             , cs1 <> cs2 <> cs3 <> [Implicit t0 (getTag t1) set] )

    ELam _ pat expr -> do
        (t0, ts) <- inferRep pat
        (t1, as1, cs1) <- local (monosetInsertSet (getVar <$> ts)) expr
        let cs2 = [Equality s t | v :>: s <- ts, w :>: t <- as1, v == w]
        pure ( tagLam (t0 `tArr` getTag t1) (setRepType t0 pat) t1
             , removeAssumptionSet ts as1 
             , cs1 <> cs2 )

inferRep :: (MonadSupply Name m) => Rep t -> m (Type, [TypeAssumption])
inferRep = cata $ \case
    RVar _ var -> do
        name <- supply
        let t = tVar kStar name 
        pure (t, [var :>: t])

--inferApp 
--  :: (MonadSupply Name m) 
--  => m (Expr Type p, [TypeAssumption], [Constraint]) 
--  -> m (Expr Type p, [TypeAssumption], [Constraint]) 
--  -> m (Expr Type p, [TypeAssumption], [Constraint])
inferApp 
  :: (MonadSupply Name m) 
  => m (Expr Type p q, [TypeAssumption], [Constraint]) 
  -> m (Expr Type p q, [TypeAssumption], [Constraint]) 
  -> m (Expr Type p q, [TypeAssumption], [Constraint])
inferApp expr1 expr2 = do
    name <- supply
    let t = tVar kStar name 
    (t1, as1, cs1) <- expr1
    (t2, as2, cs2) <- expr2
    pure ( tagApp t [t1, t2]
         , as1 <> as2
         , cs1 <> cs2 <> [Equality (getTag t1) (getTag t2 `tArr` t)] )
