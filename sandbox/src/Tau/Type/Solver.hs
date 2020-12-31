{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Solver where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Supply
import Data.Foldable (foldlM, foldrM, traverse_)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.List (nub, delete, find)
import Tau.Env (Env(..))
import Data.Set.Monad (Set, union, intersection, (\\))
import Debug.Trace
import Tau.Env (Env)
import Tau.Type
import Tau.Type.Inference
import Tau.Type.Substitution
import Tau.Type.Unification
import Tau.Util
import qualified Tau.Env as Env
import qualified Data.Set.Monad as Set
import qualified Data.Map.Strict as Map

isSolvable :: [Constraint] -> Constraint -> Bool
isSolvable cs (Implicit _ t2 (Monoset mono)) = Set.null vars where
    vars = free t2 \\ mono `intersection` active cs
isSolvable _ _ = True

choice :: [Constraint] -> Maybe ([Constraint], Constraint)
choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]

runUnify :: ExceptT TypeError Infer a -> Infer a
runUnify m = runExceptT (withExceptT TypeError m) >>= liftEither

--type BindingMap = Env [Binding]
type BindingMap = Env [Assumption Type]

solve :: [Constraint] -> Infer (Substitution, BindingMap)
solve = flip runStateT mempty . solver

solver :: [Constraint] -> StateT BindingMap Infer Substitution
solver [] = pure mempty
solver conss = do
    (cs, c) <- maybe (throwError CannotSolve) pure (choice conss)
    case c of 
        Equality t1 t2 -> do
            sub1 <- mapStateT runUnify (unify t1 t2)
            blapp sub1
            sub2 <- solver (apply sub1 cs)
            pure (sub2 <> sub1)

        Implicit t1 t2 (Monoset vars) -> do
            t3 <- generalize vars t2
            solver (Explicit t1 t3:cs)

        Explicit t1 scheme -> do
            t2 <- instantiate scheme
            traceShowM t1
            traceShowM t2
            solver (Equality t1 t2:cs)

blapp :: Substitution -> StateT BindingMap Infer ()
blapp sub = do 
    modify (Env . Map.map (apply sub) . Map.mapKeys fn . getEnv)
  where
    fn k = case Map.lookup k (getSubst sub) of
        Just (Fix (TVar _ v)) -> v
        _                     -> k



bazoo t = runStateT (generalize mempty t)
bazoo2 = bazoo (tInt `tArr` tVar kStar "a" `tArr` tVar kStar "b"  `tArr` tVar (kArr kStar kStar) "c")
    (Env.fromList [ 
      ("a", [ "toString" :>: (tVar kStar "a" `tArr` tCon kStar "String") ]) 
    , ("c", [ "isZero"   :>: (tVar kStar "c" `tArr` tCon kStar "Bool")   ])
    ])
bazoo3 = s where Right (s, _) = runInfer bazoo2

bazoo8 = runStateT (instantiate bazoo3) mempty
bazoo9 = runInfer bazoo8

generalize :: Set Name -> Type -> StateT BindingMap Infer Scheme
generalize set ty = do
    (t, sub, _) <- foldrM go (sMono ty, nullSubst, 0) [p | p <- vars ty, fst p `Set.notMember` set]
    pure (apply sub t)
  where
    go (v, k) (t, sub, n) = do
        env <- get
        let os = fromMaybe [] (Env.lookup v env)
        pure (sForall k os t, v `mapsTo` tGen n <> sub, succ n)

    vars :: Type -> [(Name, Kind)]
    vars ty = nub . flip cata ty $ \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        ty         -> []

--fazoo  = runStateT (instantiate foo) mempty
--fazoo2 = runInfer fazoo 
--foo = sForall (kArr kStar kStar) [] (sForall kStar [] (sMono (tGen 0 `tArr` tGen 1)))

instantiate :: Scheme -> StateT BindingMap Infer Type
instantiate scheme = do
    ns <- supplies (length ks)
    let ts = reverse (zipWith tVar ks ns)
    traverse_ ins (zip ns (fmap (replaceBinding ts <$>) (bindings ts)))
    pure (replaceBound ts ty)
  where
    ks = kinds scheme
    ins (n, os) = modify (Env.insert n os)

    bindings ts = flip cata scheme $ \case
        Forall _ os oss -> os:oss
        Mono t          -> []

    ty = flip cata scheme $ \case
        Mono t       -> t
        Forall _ _ t -> t

    kinds = cata $ \case
        Mono t        -> []
        Forall k _ ks -> k:ks

    replaceBound :: [Type] -> Type -> Type 
    replaceBound ts = cata $ \case
        TGen n     -> ts !! n
        TArr t1 t2 -> tArr t1 t2
        TApp t1 t2 -> tApp t1 t2
        TVar k var -> tVar k var
        TCon k con -> tCon k con

    --replaceBinding :: [Type] -> Binding -> Binding
    --replaceBinding ts (Binding name ty) = Binding name (replaceBound ts ty) 

    replaceBinding :: [Type] -> Assumption Type -> Assumption Type
    replaceBinding ts (name :>: ty) = name :>: replaceBound ts ty

--solver :: [Constraint] -> Infer Substitution
--solver [] = pure mempty
--solver cs0 = do
--    (cs, c) <- maybe (throwError CannotSolve) pure (choice cs0)
--    case c of
--        Equality t1 t2 -> do
--            sub1 <- runUnify (unify t1 t2)
--            sub2 <- solver (apply sub1 cs)
--            pure (sub2 <> sub1)
--
--        Implicit t1 t2 (Monoset vars) ->
--            solver (Explicit t1 (generalize vars t2):cs)
--
--        Explicit t1 scheme -> do
--            t2 <- instantiate scheme
--            solver (Equality t1 t2:cs)
--
----solve :: [Constraint] -> Infer (Substitution, [TypeClass])
----solve = flip runStateT [] . solver
----  where
----    solver :: [Constraint] -> StateT [TypeClass] Infer Substitution
----    solver [] = pure mempty
----    solver cs0 = do
----        traceShowM cs0
----        (cs, c) <- maybe (throwError CannotSolve) pure (choice cs0)
----        case c of
----            Equality t1 t2 -> do
----                sub1 <- mapStateT runUnify (unify t1 t2)
----                modify (apply sub1)
----                sub2 <- solver (apply sub1 cs)
----                pure (sub2 <> sub1)
----
----            Implicit t1 t2 (Monoset vars) ->
----                solver (Explicit t1 (generalize vars t2):cs)
----
----            Explicit t1 scheme -> do
----                (t2, ps1) <- instantiate scheme
----                modify (<> ps1)
----                solver (Equality t1 t2:cs)

--generalize :: Set Name -> Type -> Scheme
--generalize set ty = Forall ks (apply s qt) where
--    qt = [] :=> ty
--    (vs, ks) = unzip [(v, k) | (v, k) <- vars ty, v `Set.notMember` set]
--    s = fromList (zip vs (tGen <$> [0..]))
--
--vars :: Type -> [(Name, Kind)]
--vars ty = nub . flip cata ty $ \case
--    TVar k var -> [(var, k)]
--    TArr t1 t2 -> t1 <> t2
--    TApp t1 t2 -> t1 <> t2
--    ty         -> mempty
--
--instantiate :: (MonadSupply Name m) => Scheme -> m (Type, [TypeClass])
--instantiate (Forall ks s@(ps :=> t)) = do
--    ts <- traverse freshVar ks
--    pure (replaceBound ts t, instConstraint ts <$> ps)
--  where
--    freshVar k = tVar k <$> supply
--    instConstraint ts (TypeClass name ty) = TypeClass name (replaceBound ts ty)
--
--replaceBound :: [Type] -> Type -> Type 
--replaceBound ts = cata $ \case
--    TGen n     -> ts !! n
--    TArr t1 t2 -> tArr t1 t2
--    TApp t1 t2 -> tApp t1 t2
--    TVar k var -> tVar k var
--    TCon k con -> tCon k con
