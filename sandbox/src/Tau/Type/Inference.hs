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
import Control.Monad.Writer
import Data.Foldable (foldrM, foldl')
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set, union, intersection, (\\))
import Tau.Expr
import Tau.Expr.Patterns
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
    | TypeError TypeError
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

infer :: PatternExpr t -> Infer (RepExpr Type, [TypeAssumption], [Constraint])
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
        (tr, as0) <- inferRep pat
        (e1, as1, cs1) <- expr1
        (e2, as2, cs2) <- expr2
        set <- ask
        let cs3 = [Implicit t u set | v :>: t <- as2, (w, u) <- repVars tr, v == w]
        pure ( tagLet (getTag e2) tr e1 e2
             , as1 <> removeAssumptionSet (free tr) as2
             , cs1 <> cs2 <> [Equality (getRepTag tr) (getTag e1) ] <> cs3 )

    ELam _ pat expr -> do
        (tr, as0) <- inferRep pat
        (e1, as1, cs1) <- local (monosetInsertSet (getVar <$> as0)) expr
        let cs2 = [Equality t u | v :>: t <- as1, (w, u) <- repVars tr, v == w]
        pure ( tagLam (getRepTag tr `tArr` getTag e1) tr e1
             , removeAssumptionSet (free tr) as1
             , cs1 )

    EIf _ _ _ _ ->
        undefined

    EAnd _ _ ->
        undefined

    EOr _ _ ->
        undefined

    EMatch _ exs eqs -> do
        name <- supply
        let t = tVar kStar name 
        (es1, as1, cs1) <- unzip3 <$> sequence exs
        (eqs, as2, cs2) <- unzip3 <$> traverse inferEquation eqs
        let cs3 = do
            Equation ps exs e <- eqs
            e1 <- exs
            (p, e2) <- zip ps es1
            pure [ Equality t (getTag e)
                 , Equality tBool (getTag e1)
                 , Equality (getRepTag p) (getTag e2) 
                 ]
        pure ( tagMatch t es1 eqs
             , concat as1 <> concat as2
             , concat (cs1 <> cs2 <> cs3) )

    EOp (OEq a b) -> do
        (e1, as1, cs1) <- a
        (e2, as2, cs2) <- b
        pure (tagEq e1 e2, as1 <> as2, cs1 <> cs2)

inferEquation 
  :: Equation (Pattern t) (Infer (RepExpr Type, [Assumption Type], [Constraint])) 
  -> Infer (RepEq Type, [TypeAssumption], [Constraint])
inferEquation (Equation ps exs e) = do
    let (qs, cs) = patternReps ps
    (trs, as0) <- unzip <$> traverse inferRep qs
    let insertMono = local (monosetInsertSet (getVar <$> concat as0))

    (es1, as1, cs1) <- unzip3 <$> traverse (insertMono . infer) cs
    (es2, as2, cs2) <- unzip3 <$> sequence (insertMono <$> exs)
    (exp, as3, cs3) <- insertMono e

    let asall = concat (as1 <> as2) <> as3
    let cs4 = [Equality t u | v :>: t <- asall, (w, u) <- repVars =<< trs, v == w]

    pure ( Equation trs (es1 <> es2) exp
         , concat as0 <> removeAssumptionSet (free trs) asall
         , concat (cs1 <> cs2) <> cs3 <> cs4 )

inferRep :: Rep t -> Infer (Rep Type, [TypeAssumption])
inferRep = cata alg where
    alg rep = do
        name <- supply
        let t = tVar kStar name 
        case rep of
            RVar _ var -> 
                pure (rVar t var, [var :>: t])

            RCon _ con rs -> do
                (trs, as) <- unzip <$> sequence rs
                pure (rCon t con trs, concat as <> [con :>: t])

inferApp 
  :: Infer (Expr Type p q, [TypeAssumption], [Constraint]) 
  -> Infer (Expr Type p q, [TypeAssumption], [Constraint]) 
  -> Infer (Expr Type p q, [TypeAssumption], [Constraint])
inferApp expr1 expr2 = do
    name <- supply
    let t = tVar kStar name 
    (t1, as1, cs1) <- expr1
    (t2, as2, cs2) <- expr2
    pure ( tagApp t [t1, t2]
         , as1 <> as2
         , cs1 <> cs2 <> [Equality (getTag t1) (getTag t2 `tArr` t)] )
