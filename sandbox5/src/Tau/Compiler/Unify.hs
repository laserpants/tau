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

--xxxType :: Type -> Type
--xxxType = para $ \case
--    TVar k var   -> tVar k var
--    TCon k con   -> tCon k con
--    TArr t1 t2   -> tArr (snd t1) (snd t2)
--    TApp k t1 t2 
--        | isRowType t -> rebuildRow (finalRow t) (foldr (uncurry f) mempty (rowFields t))
--        | otherwise   -> tApp k (snd t1) (snd t2)
--      where 
--        t = tApp kRow (fst t1) (fst t2)
--        f name ty = Map.insertWith (<>) (getLabel name) [ty]
--        getLabel  = fromJust <<< Text.stripSuffix "}" <=< Text.stripPrefix "{"
--
--        rebuildRow :: Type -> Map Name [Type] -> Type
--        rebuildRow = Map.foldrWithKey (flip . foldr . tRowExtend)
--
--        rowFields :: Type -> [(Name, Type)]
--        rowFields = para $ \case
--            TApp _ (Fix (TCon _ con), _) t -> [(con, fst t)]
--            TApp _ a b                     -> snd a <> snd b
--            TArr a b                       -> snd a <> snd b
--            TVar{}                         -> []
--            _                              -> []
--
--        finalRow :: Type -> Type
--        finalRow = cata $ \case
--            TApp _ _ t                     -> t
--            t                              -> embed t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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
    fn TRow{} TRow{}                          = unifyRowTypes unifyTypePairs t u
    fn (TVar kind name) _                     = bindType name kind u
    fn _ (TVar kind name)                     = bindType name kind t
    fn (TCon k1 a) (TCon k2 b) | a == b       = (mempty ,) <$> unifyKinds k1 k2
    fn _ _                                    = throwError IncompatibleTypes

--fool (TRow a t1 t2) (TRow b u1 u2) | a == b = do
--    (typeSub1, kindSub1) <- unifyTypes t1 u1
--    (typeSub2, kindSub2) <- unifyRowTypes (apply kindSub1 (apply typeSub1 t2))
--                                          (apply kindSub1 (apply typeSub1 u2))
--    pure (typeSub2 <> typeSub1, kindSub2 <> kindSub1)
--
--fool t u = unifyTypes (embed t) (embed u)
--
--    (typeSub1, kindSub1) <- unifyTypes t1 u1
--    (typeSub2, kindSub2) <- unifyTypes (apply kindSub1 (apply typeSub1 t2))
--                                       (apply kindSub1 (apply typeSub1 u2))
--    pure (typeSub2 <> typeSub1, kindSub2 <> kindSub1)

--matchRowTypes = undefined

--unifyTypes
--  :: (MonadError UnificationError m)
--  => Type
--  -> Type
--  -> m (Substitution Type, Substitution Kind)
--unifyTypes t u
--    | isRowType t || isRowType u              = unifyRowTypes t u
--    | otherwise                               = unifyTypesImpl t u
--
--unifyTypesImpl
--  :: (MonadError UnificationError m)
--  => Type
--  -> Type
--  -> m (Substitution Type, Substitution Kind)
--unifyTypesImpl t u = fn (project t) (project u)
--  where
--    fn (TArr t1 t2) (TArr u1 u2)              = unifyTypePairs (t1, t2) (u1, u2)
--    fn (TApp _ t1 t2) (TApp _ u1 u2)          = unifyTypePairs (t1, t2) (u1, u2)
--    fn (TVar kind name) _                     = bindType name kind u
--    fn _ (TVar kind name)                     = bindType name kind t
--    fn _ _ | t == u                           = pure mempty
--    fn _ _                                    = throwError IncompatibleTypes

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
    fn TRow{} TRow{}                          = unifyRowTypes matchTypePairs t u
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

unifyRowTypes 
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => ((Type, Type) -> (Type, Type) -> m (Substitution Type, Substitution Kind))
  -> Type
  -> Type
  -> m (Substitution Type, Substitution Kind)
unifyRowTypes unifyPairs t u = 
    unifyRowTypes_ (mapRep t, final t) (mapRep u, final u)
  where
    mapRep = foldr (uncurry (Map.insertWith (<>))) mempty 
        . (second pure <$>) 
        . rowFields 

unifyRowTypes_
  :: ( MonadSupply Name m
     , MonadError UnificationError m )
  => (Map Name [Type], Type)
  -> (Map Name [Type], Type)
  -> m (Substitution Type, Substitution Kind)
unifyRowTypes_ (m1, j) (m2, k) 
    | Map.null m1 && Map.null m2 = unifyTypes j k
    | Map.null m1 = unifyTypes j (Map.foldrWithKey (flip . foldr . tRow) k m2)
    | otherwise = 
        case Map.lookup a m2 of
            Just (u:us) -> do
                (typeSub1, kindSub1) <- unifyRowTypes_ (updateMap m1 ts, j) (updateMap m2 us, k)
                (typeSub2, kindSub2) <- unifyTypes (apply kindSub1 (apply typeSub1 t)) (apply kindSub1 (apply typeSub1 u))
                pure (typeSub2 <> typeSub1, kindSub2 <> kindSub1)

            _ -> do
                ta <- newTVar_
                when (k == j) $ throwError IncompatibleTypes
                let q = tRow a t ta
                (typeSub1, kindSub1) <- unifyRowTypes_ (updateMap m1 ts, j) (m2, ta)
                (typeSub2, kindSub2) <- unifyTypes (apply kindSub1 (apply typeSub1 k)) q 
                pure (typeSub2 <> typeSub1, kindSub2 <> kindSub1)

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

--unifyRowTypes unifyPairs t u = fn (project t) (project u)
--  where
--    fn (TRow a t1 t2) (TRow b u1 u2) | a == b = unifyPairs (t1, t2) (u1, u2)
--    fn (TRow a t1 t2) (TRow b u1 u2) = do
--        case (t1:gork t2, gork u2) of
--            _ ->
--                undefined
----        case Map.lookup a mapRep of
----            -Just (t:ts) ->
----            --    unifyPairs (t1, t2) (t, fromMap (final u2) (Map.insert a ts mapRep)) -- yyy (Map.delete a xxx)) -- yyy (Map.delete a xxx)
----            Nothing -> 
----                undefined
----        --case lookup a (foldr (Map.insertWith (<>)) mempty (rowFields u2)) of
----        --    Just t -> undefined -- unifyPairs (t1, t2) (t, filter (\x -> fst x /= a) u2)
----        --    Nothing -> undefined
----      where
----        mapRep = foldr (uncurry f) mempty (rowFields u2)
----        f name ty = Map.insertWith (<>) name [ty]
----        fromMap = Map.foldrWithKey (flip . foldr . tRow)
--      where
--        gork t = snd <$> filter ((== a) . fst) (rowFields t)

--unifyRowTypes 
--  :: (MonadError UnificationError m)
--  => ((Type, Type) -> (Type, Type) -> m (Substitution Type, Substitution Kind))
--  -> Type
--  -> Type
--  -> m (Substitution Type, Substitution Kind)
--unifyRowTypes g t u = do
--    traceShowM zzz1
--    traceShowM zzz2
--    traceShowM "-----------"
--    g zzz1 zzz2
--  where
--    a1 = rowFields t
--    b1 = baseRow t
--    keys1 = fst <$> a1
--    m1 :: Map Name [Type]
--    m1 = foldr (uncurry f) mempty a1
--    (x1, y1) = foo m1
--    zzz1 :: (Type, Type)
--    zzz1 = (fromMap tRowNil x1, fromMap b1 y1)
--
--    a2 = rowFields u
--    b2 = baseRow u
--    keys2 = fst <$> a2
--    m2 :: Map Name [Type]
--    m2 = foldr (uncurry f) mempty a2
--    (x2, y2) = foo m2
--    zzz2 :: (Type, Type)
--    zzz2 = (fromMap tRowNil x2, fromMap b2 y2)
--
--    foo = Map.partitionWithKey (\k _ -> k `elem` intersect keys1 keys2)
--    f name ty = Map.insertWith (<>) name [ty]
--
--fromMap :: Type -> Map Name [Type] -> Type
--fromMap = Map.foldrWithKey (flip . foldr . tRow)

rowFields :: Type -> [(Name, Type)]
rowFields = para $ \case
    TRow label ty rest             -> (label, fst ty):snd rest
    _                              -> []

final :: Type -> Type
final = cata $ \case
    TRow _ _ r                     -> r
    t                              -> embed t

--unifyRowTypes
--  :: (MonadError UnificationError m)
--  => Type
--  -> Type
--  -> m (Substitution Type, Substitution Kind)
--unifyRowTypes = rowUnify unifyTypePairs

--matchRowTypes
--  :: (MonadError UnificationError m)
--  => Type
--  -> Type
--  -> m (Substitution Type, Substitution Kind)
--matchRowTypes = rowUnify matchTypePairs
--
--rowUnify :: ((Type, Type) -> (Type, Type) -> t) -> Type -> Type -> t
--rowUnify f t u = traceShow map1 $ traceShow "---" $ traceShow map2 $ f (go t map1) (go u map2)
--  where
--    (map1, keys1) = toMap t
--    (map2, keys2) = toMap u
--    go ty = (fromMap tRowNil *** fromMap (getBaseRow ty)) 
--        . Map.partitionWithKey (\k _ -> k `elem` intersect keys1 keys2)
--
--    fromMap :: Type -> Map Name [Type] -> Type
--    fromMap = Map.foldrWithKey (flip . foldr . tRow)
--
--    toMap :: Type -> (Map Name [Type], [Name])
--    toMap t = (tmap, Map.keys tmap)
--      where
--        tmap      = foldr (uncurry f) mempty (getRowExts t)
--        f name ty = Map.insertWith (<>) (getLabel name) [ty]
--        getLabel  = fromJust <<< Text.stripSuffix "}" <=< Text.stripPrefix "{"
--
--    getRowExts :: Type -> [(Name, Type)]
--    getRowExts = para $ \case
--        TApp _ (Fix (TCon _ con), _) t -> [(con, fst t)]
--        TApp _ a b                     -> snd a <> snd b
--        TArr a b                       -> snd a <> snd b
--        TVar{}                         -> []
--        _                              -> []
--
--    getBaseRow :: Type -> Type
--    getBaseRow = cata $ \case
--        TApp _ _ t                     -> t
--        t                              -> embed t

--toMap :: Type -> Map Name [Type]
--toMap t =
--    foldr (\(name, ty) -> Map.insertWith (<>) (getLabel name) [ty])
--        mempty (foldType t)
--  where
--    getLabel = fromJust <<< Text.stripSuffix "}" <=< Text.stripPrefix "{"
--
--    foldType :: Type -> [(Name, Type)]
--    foldType = para $ \case
--        TApp _ (Fix (TCon _ con), _) t -> [(con, fst t)]
--        TApp _ a b                     -> snd a <> snd b
--        TArr a b                       -> snd a <> snd b
--        TVar{}                         -> []
--        _                              -> []
--
--flattenMap :: Map Name [Type] -> Map Name [Type]
--flattenMap tmap =
--    case Map.lookup "*" tmap of
----        Just [t] -> Map.foldrWithKey
----                        (Map.insertWith (<>))
----                        (Map.delete "*" tmap)
----                        (toMap (canonicalizeRowTypes t))
--        _ -> tmap
--
--fromMap :: Map Name [Type] -> Type
--fromMap = Map.foldrWithKey (flip . foldr . tRowExtend) tRowNil
--
--
--data RowTypes a
--    = RNil
--    | RVar a
--    | RExt
--    deriving (Show, Eq)
--
--rowType :: Row Type -> RowTypes Name
--rowType (Row m Nothing)  | null m = RNil
--rowType (Row m (Just r)) | null m = RVar (unsafeGetTypeVar r)
--rowType _                         = RExt
--
--setKind :: Kind -> Type -> Type
--setKind kind = cata $ \case
--    TVar _ var -> tVar kind var
--    TCon _ con -> tCon kind con
--    t          -> embed t
--
--bind :: (MonadError UnificationError m) => Name -> Kind -> Type -> m TypeSubstitution
----bind name kind ty
----    | "a5" == name = traceShow kind $ traceShow ty $ undefined
----
--bind name kind ty
--    | ty == tVar kind name                    = pure mempty
--    | name `elem` free ty                     = throwError InfiniteType
--    | kHole == kind                           = pure (name `mapsTo` ty)
--    | kHole == kindOf ty                      = pure (name `mapsTo` setKind kind ty)
--    | kind /= kindOf ty                       = throwError KindMismatch
--    | otherwise                               = pure (name `mapsTo` ty)
--
--unify :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
--unify t u
--    | isRow t || isRow u                      = unifyRowTypess t u
--    | otherwise                               = fn (project t) (project u)
--  where
--    fn (TArr t1 t2) (TArr u1 u2)              = unifyTypePairs (t1, t2) (u1, u2)
--    fn (TApp t1 t2) (TApp u1 u2)              = unifyTypePairs (t1, t2) (u1, u2)
--    fn (TVar kind name) _                     = bind name kind u
--    fn _ (TVar kind name)                     = bind name kind t
--    fn _ _ | t == u                           = pure mempty
--    fn _ _                                    = throwError IncompatibleTypes
--
--match :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
--match t u
--    | isRow t || isRow u                      = matchRowTypess t u
--    | otherwise                               = fn (project t) (project u)
--  where
--    fn (TArr t1 t2) (TArr u1 u2)              = matchTypePairs (t1, t2) (u1, u2)
--    fn (TApp t1 t2) (TApp u1 u2)              = matchTypePairs (t1, t2) (u1, u2)
--    fn (TVar kind name) _                     = bind name kind u
--    fn _ _ | t == u                           = pure mempty
--    fn _ _                                    = throwError IncompatibleTypes
--
--unifyRowTypess :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
--unifyRowTypess t u = fn (rowType r) (rowType s)
--  where
--    fn RNil RNil                              = pure mempty
--    fn (RVar var) _                           = bind var kRow u
--    fn _ (RVar var)                           = bind var kRow t
--    fn _ _                                    = unifyRows r s
--    r                                         = typeToRow t
--    s                                         = typeToRow u
--
--matchRowTypess :: (MonadError UnificationError m) => Type -> Type -> m TypeSubstitution
--matchRowTypess t u = fn (rowType r) (rowType s)
--  where
--    fn RNil RNil                              = pure mempty
--    fn (RVar var) _                           = bind var kRow u
--    fn _ _                                    = matchRows r s
--    r                                         = typeToRow t
--    s                                         = typeToRow u
--
--unifyTypePairs :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
--unifyTypePairs (t1, t2) (u1, u2) = do
--    sub1 <- unify t1 u1
--    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
--    pure (sub2 <> sub1)
--
--matchTypePairs :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m TypeSubstitution
--matchTypePairs (t1, t2) (u1, u2) = do
--    sub1 <- match t1 u1
--    sub2 <- match t2 u2
--    merge sub1 sub2 & maybe (throwError MergeFailed) pure
--
--unifyRows :: (MonadError UnificationError m) => Row Type -> Row Type -> m TypeSubstitution
--unifyRows (Row m1 Nothing) (Row m2 Nothing)
--    | Map.null m1 && Map.null m2              = pure mempty
--unifyRows (Row m (Just r)) row | Map.null m   = bind (unsafeGetTypeVar r) kRow (rowToType row)
--unifyRows row (Row m (Just r)) | Map.null m   = bind (unsafeGetTypeVar r) kRow (rowToType row)
--unifyRows r1 r2 = do
--    (sub1, sub2) <- rowSubs unifyRows unifyWith r1 r2
--    pure (sub2 <> sub1)
--  where
--    unifyWith (t, u) sub = unify (apply sub t) (apply sub u)
--
--matchRows :: (MonadError UnificationError m) => Row Type -> Row Type -> m TypeSubstitution
--matchRows (Row m1 Nothing) (Row m2 Nothing)
--    | Map.null m1 && Map.null m2              = pure mempty
--matchRows (Row m (Just r)) row | Map.null m   = bind (unsafeGetTypeVar r) kRow (rowToType row)
--matchRows r1 r2 = do
--    (sub1, sub2) <- rowSubs matchRows matchWith r1 r2
--    merge sub1 sub2 & maybe (throwError MergeFailed) pure
--  where
--    matchWith (t, u) sub1 = do
--        sub2 <- match t u
--        merge sub1 sub2 & maybe (throwError MergeFailed) pure
--
--rowSubs
--  :: (MonadError UnificationError m)
--  => (Row Type -> Row Type -> m TypeSubstitution)
--  -> ((Type, Type) -> TypeSubstitution -> m TypeSubstitution)
--  -> Row Type
--  -> Row Type
--  -> m (TypeSubstitution, TypeSubstitution)
--rowSubs combineRows unifyFun (Row m1 r1) (Row m2 r2)
--    | null mutualKeys = throwError IncompatibleRows
--    | otherwise = do
--        sub1 <- combineRows (Row (unique m1) r1) (Row (unique m2) r2)
--        sub2 <- foldrM combine sub1 mutualKeys
--        pure (sub1, sub2)
--  where
--    mutualKeys    = Map.keys m1 `intersect` Map.keys m2
--    unique        = Map.filterWithKey (\k -> const (k `notElem` mutualKeys))
--    combine k sub = foldrM unifyFun sub (zip (m1 ! k) (m2 ! k))
