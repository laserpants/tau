{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TupleSections     #-}
module Tau.Compiler.Unify where

import Control.Applicative ((<|>))
import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List (intersect, (\\))
import Data.Map.Strict (Map, (!))
import Data.Maybe (fromJust)
import Data.Tuple.Extra (first, second)
import Tau.Compiler.Error
import Tau.Compiler.Substitute hiding (null)
import Tau.Lang
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

bindKind
  :: (MonadError UnificationError m)
  => Name
  -> Kind
  -> m (Substitution Kind)
bindKind name kind
    | getKindVar kind == Just name            = pure mempty
    | name `elem` kindVars kind               = throwError InfiniteKind
    | otherwise                               = pure (name `mapsTo` kind)

unifyKinds
  :: (MonadError UnificationError m)
  => Kind
  -> Kind
  -> m (Substitution Kind)
unifyKinds k l = fn (project k) (project l)
  where
    fn (KArr k1 k2) (KArr l1 l2)              = unifyKindPairs (k1, k2) (l1, l2)
    fn (KVar name) _                          = bindKind name l
    fn _ (KVar name)                          = bindKind name k
    fn _ _ | k == l                           = pure mempty
    fn _ _                                    = throwError IncompatibleKinds

unifyKindPairs
  :: (MonadError UnificationError m)
  => (Kind, Kind)
  -> (Kind, Kind)
  -> m (Substitution Kind)
unifyKindPairs (k1, k2) (l1, l2) = do
    sub1 <- unifyKinds k1 l1
    sub2 <- unifyKinds (apply sub1 k2) (apply sub1 l2)
    pure (sub2 <> sub1)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

bindType
  :: (MonadError UnificationError m)
  => Name
  -> Kind
  -> Type
  -> m (Substitution Type, Substitution Kind)
bindType name kind ty
    | getTypeVar ty == Just name              = withTypeSub mempty
    | name `elem` (fst <$> free ty)           = throwError InfiniteType
    | otherwise                               = withTypeSub (name `mapsTo` ty)
  where
    withTypeSub sub = do
        kindSub <- unifyKinds kind (kindOf ty)
        pure (sub, kindSub)

unifyTypes
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
unifyTypes t u = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = unifyTypePairs (t1, t2) (u1, u2)
    fn (TApp _ t1 t2) (TApp _ u1 u2)          = unifyTypePairs (t1, t2) (u1, u2)
    fn TRow{} TRow{}                          = unifyRows unifyTypes unifyTypePairs t u
    fn (TVar kind name) _                     = bindType name kind u
    fn _ (TVar kind name)                     = bindType name kind t
    fn (TCon k1 a) (TCon k2 b) | a == b       = (mempty ,) <$> unifyKinds k1 k2
    fn _ _                                    = throwError IncompatibleTypes

matchTypes
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
matchTypes t u = fn (project t) (project u)
  where
    fn (TArr t1 t2) (TArr u1 u2)              = matchTypePairs (t1, t2) (u1, u2)
    fn (TApp _ t1 t2) (TApp _ u1 u2)          = matchTypePairs (t1, t2) (u1, u2)
    fn TRow{} TRow{}                          = unifyRows matchTypes matchTypePairs t u
    fn (TVar kind name) _                     = bindType name kind u
    fn _ _ | t == u                           = pure mempty
    fn _ _                                    = throwError IncompatibleTypes

unifyTypePairs
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => (Type, Type)
  -> (Type, Type)
  -> m (Substitution Type, Substitution Kind)
unifyTypePairs (t1, t2) (u1, u2) = do
    (typeSub1, kindSub1) <- unifyTypes t1 u1
    (typeSub2, kindSub2) <- unifyTypes (apply kindSub1 (apply typeSub1 t2))
                                       (apply kindSub1 (apply typeSub1 u2))
    pure (typeSub2 <> typeSub1, kindSub2 <> kindSub1)

matchTypePairs
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => (Type, Type)
  -> (Type, Type)
  -> m (Substitution Type, Substitution Kind)
matchTypePairs (t1, t2) (u1, u2) = do
    (typeSub1, kindSub1) <- matchTypes t1 u1
    (typeSub2, kindSub2) <- matchTypes t2 u2
    (,) <$> fn typeSub1 typeSub2 <*> fn kindSub1 kindSub2
  where
    fn sub1 sub2 = maybe (throwError MergeFailed) pure (merge sub1 sub2)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

unifyRows 
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => (Type -> Type -> m (Substitution Type, Substitution Kind))
  -> ((Type, Type) -> (Type, Type) -> m (Substitution Type, Substitution Kind))
  -> Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
unifyRows combineTypes combinePairs t u = 
    fn (mapRep t, final t) (mapRep u, final u)
  where
    mapRep = foldr (uncurry (Map.insertWith (<>))) mempty 
        . (second pure <$>) 
        . rowFields 

    rowFields :: Type -> [(Name, Type)]
    rowFields = para $ \case
        TRow label ty rest             -> (label, fst ty):snd rest
        _                              -> []

    final :: Type -> Type
    final = cata $ \case
        TRow _ _ r                     -> r
        t                              -> embed t

    fromMap :: Type -> Map Name [Type] -> Type
    fromMap = Map.foldrWithKey (flip . foldr . tRow)

    fn (m1, j) (m2, k) 
        | Map.null m1 && Map.null m2 = combineTypes j k
        | Map.null m1 = combineTypes j (fromMap k m2)
        | otherwise = 
            case Map.lookup a m2 of
                Just (u:us) -> 
                    combinePairs 
                        (fromMap j (updateMap m1 ts), t) 
                        (fromMap k (updateMap m2 us), u)
                _ -> do
                    ta <- newTVar_
                    when (k == j) $ throwError IncompatibleTypes
                    combinePairs 
                        (fromMap j (updateMap m1 ts), k) 
                        (fromMap ta m2, tRow a t ta)
      where
        (a, t:ts) = Map.elemAt 0 m1
        updateMap m = \case
            [] -> Map.delete a m
            ts -> Map.insert a ts m

newTVar_ :: (MonadSupply Name m) => m (TypeT a)
newTVar_ = do
    k <- ("k" <>) <$> supply
    t <- ("a" <>) <$> supply
    pure (tVar (kVar k) t)
