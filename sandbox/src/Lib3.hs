{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE FlexibleContexts     #-}
module Lib3 where

import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable
import Data.List (delete)
import Data.Set.Monad ((\\))
import Data.Map.Strict (Map)
import Data.Maybe
import Data.Set.Monad (Set)
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

type Name1 = String

data Type1 v
    = TVar1 v
    | TGen1 Int
    | TCon1 String 
    | TArr1 (Type1 v) (Type1 v)
    | TApp1 (Type1 v) (Type1 v)
    deriving (Show, Eq, Ord)

data Scheme1 v = Forall1 [Name1] (Type1 v)
    deriving (Show, Eq, Ord)

xxx :: Type1 ([Name1], Name1) -> ([Name1], Type1 Name1)
xxx (TVar1 (xs, t)) = (xs, TVar1 t)
xxx (TCon1 con)     = ([], TCon1 con)
xxx (TArr1 t1 t2) = let (xs, u1) = xxx t1; (ys, u2) = xxx t2 in (xs <> ys, TArr1 u1 u2)
xxx (TApp1 t1 t2) = let (xs, u1) = xxx t1; (ys, u2) = xxx t2 in (xs <> ys, TApp1 u1 u2)

yyy :: ([Name1], Type1 Name1) -> Type1 ([Name1], Name1)
yyy (xs, ty) = 
    case ty of
        TVar1 var   -> TVar1 (xs, var)
        TCon1 con   -> TCon1 con
        TArr1 t1 t2 -> let abc = yyy (xs, t1); def = yyy (xs, t2) in TArr1 abc def
        TApp1 t1 t2 -> let abc = yyy (xs, t1); def = yyy (xs, t2) in TApp1 abc def

unify1 
  :: (Monad m) 
  => Type1 ([Name1], Name1) 
  -> Type1 ([Name1], Name1) 
  -> m ([Name1], Map Name1 (Type1 Name1))
unify1 (TArr1 t1 t2) (TArr1 u1 u2) = unifyPairs1 (t1, t2) (u1, u2)
unify1 (TApp1 t1 t2) (TApp1 u1 u2) = unifyPairs1 (t1, t2) (u1, u2)
unify1 (TVar1 (xs, var)) u = do
    let (ys, u1) = xxx u 
    zzz <- bind1 var u1 
    pure (xs <> ys, zzz)
unify1 t (TVar1 (xs, var)) = do
    let (ys, t1) = xxx t 
    zzz <- bind1 var t1 
    pure (xs <> ys, zzz)
unify1 t u | t == u = pure mempty
unify1 _ _ = error "CannotUnify"

unifyPairs1 
  :: (Monad m) 
  => (Type1 ([Name1], Name1), Type1 ([Name1], Name1))
  -> (Type1 ([Name1], Name1), Type1 ([Name1], Name1))
  -> m ([Name1], Map Name1 (Type1 Name1))
unifyPairs1 (t1, t2) (u1, u2) = do
    (xs, sub1) <- unify1 t1 u1
    (ys, sub2) <- unify1 (apply1 sub1 t2) (apply1 sub1 u2)
    pure (xs <> ys, compose1 sub2 sub1)

apply1 :: Map Name1 (Type1 Name1) -> Type1 ([Name1], Name1) -> Type1 ([Name1], Name1)
apply1 sub = \case 
    t@(TVar1 (xs, var)) -> 
        case Map.lookup var sub of
            Nothing -> t
            Just ty -> yyy (xs, ty)
    TArr1 t1 t2 -> TArr1 (apply1 sub t1) (apply1 sub t2)
    TApp1 t1 t2 -> TApp1 (apply1 sub t1) (apply1 sub t2)
    ty          -> ty

apply2 :: Map Name1 (Type1 Name1) -> Type1 Name1 -> Type1 Name1
apply2 sub = \case
    t@(TVar1 var) -> fromMaybe t (Map.lookup var sub) 
    TArr1 t1 t2   -> TArr1 (apply2 sub t1) (apply2 sub t2)
    TApp1 t1 t2   -> TApp1 (apply2 sub t1) (apply2 sub t2)
    ty            -> ty

compose1 :: Map Name1 (Type1 Name1) -> Map Name1 (Type1 Name1) -> Map Name1 (Type1 Name1)
compose1 s1 s2 = fmap (apply2 s1) s2 `Map.union` s1

bind1 :: (Monad m) => Name1 -> Type1 Name1 -> m (Map Name1 (Type1 Name1))
bind1 name ty
    | ty == TVar1 name       = pure mempty
    | name `elem` free1 ty   = error "InfiniteType"
--    | Just kind /= kindOf ty = throwError KindMismatch
    | otherwise              = pure (Map.singleton name ty) -- (name `mapsTo` ty)

free1 :: Type1 Name1 -> Set Name1
free1 = \case
    TVar1 v     -> Set.singleton v
    TArr1 t1 t2 -> free1 t1 <> free1 t2
    TApp1 t1 t2 -> free1 t1 <> free1 t2
    ty          -> mempty

free2 :: Pattern1 Name1 -> Set Name1
free2 = \case 
    PVar1 _ v    -> Set.singleton v
    PCon1 _ _ rs -> unions (free2 <$> rs)
    _            -> mempty

free3 :: Type1 ([Name1], Name1) -> Set Name1
free3 = \case
    TVar1 (_, v) -> Set.singleton v
    TArr1 t1 t2  -> free3 t1 <> free3 t2
    TApp1 t1 t2  -> free3 t1 <> free3 t2
    ty           -> mempty

free4 :: Scheme1 ([Name1], Name1) -> Set Name1
free4 (Forall1 _ t) = free3 t

free5 :: Set Name1 -> Set Name1
free5 = id

unions :: (Ord a) => [Set a] -> Set a
unions = foldr1 Set.union 

---
---
---

data Pattern1 t
    = PVar1 t Name1
    | PCon1 t Name1 [Pattern1 t]
    | PLit1 t Int
    | PAny1 t 
    deriving (Show, Eq, Ord)

data Expr1 t
    = EVar1 t Name1
    | ELit1 t Int
    | EApp1 t [Expr1 t]
    | ELet1 t (Pattern1 t) (Expr1 t) (Expr1 t)
    | ELam1 t (Pattern1 t) (Expr1 t)
    deriving (Show, Eq, Ord)

setPatternTag1 :: t -> Pattern1 s -> Pattern1 t
setPatternTag1 t = \case
    PVar1 _ var     -> PVar1 t var
    PCon1 _ con ps  -> PCon1 t con (setPatternTag1 t <$> ps)
    PLit1 _ lit     -> PLit1 t lit
    PAny1 _         -> PAny1 t

setTag1 :: t -> Expr1 s -> Expr1 t
setTag1 t = \case
    EVar1 _ var     -> EVar1 t var
    ELit1 _ lit     -> ELit1 t lit
    EApp1 _ exs     -> EApp1 t (setTag1 t <$> exs)
    ELet1 _ p e1 e2 -> ELet1 t (setPatternTag1 t p) (setTag1 t e1) (setTag1 t e2)
    ELam1 _ p e1    -> ELam1 t (setPatternTag1 t p) (setTag1 t e1)

data Assumption1 a = As1 Name1 a
    deriving (Show, Eq)

removeAssumption :: Name1 -> [Assumption1 a] -> [Assumption1 a]
removeAssumption name = filter (\a -> name /= assumptionVar a)

removeAssumptionSet :: Set Name1 -> [Assumption1 a] -> [Assumption1 a]
removeAssumptionSet = flip (Set.foldr removeAssumption) 

assumptionVar :: Assumption1 a -> Name1
assumptionVar (As1 name _) = name

type Monoset = Set Name1

monosetInsert :: Name1 -> Monoset -> Monoset
monosetInsert = Set.insert 

monosetInsertSet :: [Name1] -> Monoset -> Monoset
monosetInsertSet = flip (foldr monosetInsert)

data Constraint1 v
    = Equality1 (Type1 v) (Type1 v)
    | Implicit1 (Type1 v) (Type1 v) Monoset
    | Explicit1 (Type1 v) (Scheme1 v)
    deriving (Show, Eq)

patternVars :: Pattern1 t -> [(Name1, t)]
patternVars = \case
    PVar1 t var  -> [(var, t)]
    PCon1 _ _ rs -> concatMap patternVars rs
    PLit1 _ lit  -> []
    PAny1 _      -> []

infer1 
  :: (MonadReader Monoset m, MonadSupply Name1 m) 
  => Expr1 t
  -> WriterT [Constraint1 Name1] m (Expr1 Name1, [Assumption1 Name1])
infer1 = \case

    EVar1 _ var -> do
        tvar <- supply
        pure (EVar1 tvar var, [As1 var tvar])

    ELit1 _ lit -> do
        tvar <- supply
        t <- inferLiteral1 lit
        tell [Equality1 (TVar1 tvar) t] 
        pure (ELit1 tvar lit, [])

    EApp1 _ (ex:exs) ->
        foldl inferApp1 (baz ex) exs

    ELet1 _ pat expr1 expr2 -> do
        tvar <- supply
        (tp, as0) <- inferPattern1 pat
        (e1, as1) <- infer1 expr1
        (e2, as2) <- infer1 expr2
        set <- ask

        tell [ Equality1 (TVar1 tvar) (fromTag1 e2) 
             , Equality1 (fromPatternTag1 tp) (fromTag1 e1) ]

        tell $ do
            As1 v t <- as2
            (w, u) <- patternVars tp
            guard (v == w)
            pure (Implicit1 (TVar1 t) (TVar1 u) set)

        pure (ELet1 tvar tp e1 e2, as1 <> removeAssumptionSet (free2 tp) as2)

    ELam1 _ pat expr1 -> do
        tvar <- supply
        (tp, as0) <- inferPattern1 pat
        (e1, as1) <- local (monosetInsertSet (assumptionVar <$> as0)) (infer1 expr1)

        tell [Equality1 (TVar1 tvar) (TArr1 (fromPatternTag1 tp) (fromTag1 e1))]

        tell $ do
            As1 v t <- as1
            (w, u) <- patternVars tp
            guard (v == w)
            pure (Equality1 (TVar1 t) (TVar1 u))

        pure (ELam1 tvar tp e1, removeAssumptionSet (free2 tp) as1)

baz 
  :: (MonadReader Monoset m, MonadSupply Name1 m) 
  => Expr1 t 
  -> WriterT [Constraint1 Name1] m (Expr1 Name1, [Assumption1 Name1])
baz expr = pure (setTag1 "" expr, [])

inferPattern1 
  :: (MonadReader Monoset m, MonadSupply Name1 m) 
  => Pattern1 t 
  -> WriterT [Constraint1 Name1] m (Pattern1 Name1, [Assumption1 Name1])
inferPattern1 pat = do
    tvar <- supply
    case pat of
        PVar1 _ var -> 
            pure (PVar1 tvar var, [As1 var tvar])

        PCon1 _ con ps -> do
            (trs, as) <- unzip <$> traverse inferPattern1 ps
            pure (PCon1 tvar con trs, concat as <> [As1 con tvar])

        PLit1 _ lit -> do
            t <- inferLiteral1 lit
            pure (PLit1 tvar lit, [])

        PAny1 _ -> 
            pure (PAny1 tvar, [])

inferApp1 
  :: (MonadReader Monoset m, MonadSupply Name1 m) 
  => WriterT [Constraint1 Name1] m (Expr1 Name1, [Assumption1 Name1]) 
  -> Expr1 t
  -> WriterT [Constraint1 Name1] m (Expr1 Name1, [Assumption1 Name1])
inferApp1 expr1 expr2 = do
    tvar <- supply
    (e1, as1) <- expr1
    (e2, as2) <- infer1 expr2
    tell [Equality1 (fromTag1 e1) (TArr1 (fromTag1 e2) (TVar1 tvar))]
    pure (EApp1 tvar [e1, e2], as1 <> as2)

inferLiteral1 
  :: (MonadReader Monoset m, MonadSupply Name1 m) 
  => Int 
  -> WriterT [Constraint1 Name1] m (Type1 v)
inferLiteral1 _ = pure (TCon1 "Int")

fromTag1 :: Expr1 v -> Type1 v
fromTag1 = TVar1 . getTag1

fromPatternTag1 :: Pattern1 v -> Type1 v
fromPatternTag1 = TVar1 . getPatternTag1

getTag1 :: Expr1 t -> t
getTag1 (EVar1 t _)     = t
getTag1 (ELit1 t _)     = t
getTag1 (EApp1 t _)     = t
getTag1 (ELet1 t _ _ _) = t
getTag1 (ELam1 t _ _)   = t

getPatternTag1 :: Pattern1 t -> t
getPatternTag1 (PVar1 t _)   = t
getPatternTag1 (PCon1 t _ _) = t
getPatternTag1 (PLit1 t _)   = t 
getPatternTag1 (PAny1 t)     = t

inferExpr1 
  :: (MonadReader Monoset m, MonadSupply Name1 m) 
  => Expr1 t
  -> m ((Expr1 Name1, [Assumption1 Name1]), [Constraint1 Name1])
inferExpr1 = runWriterT . infer1

runInferExpr1 :: Expr1 t -> Maybe ((Expr1 Name1, [Assumption1 Name1]), [Constraint1 Name1])
runInferExpr1 e = evalSupply (runReaderT (inferExpr1 e) mempty) (numSupply1 "a")

prefixSupply1 supply prefix = fmap (prefix <>) supply
numSupply1 = prefixSupply1 (show <$> [1..])

---
---
---

isSolvable1 
  :: [Constraint1 ([Name1], Name1)] 
  -> Constraint1 ([Name1], Name1) 
  -> Bool
isSolvable1 cs (Implicit1 _ t2 set) = Set.null vars where
    vars = free3 t2 \\ set `Set.intersection` active1 cs
isSolvable1 _ _ = True

active1 :: [Constraint1 ([Name1], Name1)] -> Set Name1
active1 = join . Set.fromList . fmap active2

active2 :: Constraint1 ([Name1], Name1) -> Set Name1
active2 (Equality1 t1 t2)      = free3 t1 `Set.union` free3 t2
active2 (Implicit1 t1 t2 set)  = free3 t1 `Set.union` (free5 set `Set.intersection` free3 t2)
active2 (Explicit1 t1 scheme)  = free3 t1 `Set.union` free4 scheme

choice1 
  :: [Constraint1 ([Name1], Name1)] 
  -> Maybe ([Constraint1 ([Name1], Name1)], Constraint1 ([Name1], Name1))
choice1 cs = find (uncurry isSolvable1) [(ys, x) | x <- cs, let ys = delete x cs]

solve1 :: (MonadSupply Name1 m) => [Constraint1 ([Name1], Name1)] -> m ([Name1], Map Name1 (Type1 Name1))
solve1 [] = pure mempty
solve1 xs = do
    (cs, c) <- maybe (error "CannotSolve") pure (choice1 xs)
    case c of 
        Equality1 t1 t2 -> do
            (xs, sub1) <- unify1 t1 t2
            (ys, sub2) <- solve1 (apply3 sub1 cs)
            pure (xs <> ys, compose1 sub2 sub1)

        Implicit1 t1 t2 vars -> do
            t3 <- generalize1 vars t2
            solve1 (Explicit1 t1 t3:cs)

        Explicit1 t1 scheme -> do
            t2 <- instantiate1 scheme
            solve1 (Equality1 t1 t2:cs)

generalize1 :: (MonadSupply Name1 m) => Set Name1 -> Type1 ([Name1], Name1) -> m (Scheme1 ([Name1], Name1))
generalize1 set ty = 
    pure (Forall1 xs (apply1 sub ty))
  where
    (xs, b) = xxx ty
    vs  = filter (`Set.notMember` set) (Set.toList (free3 ty))
    sub = Map.fromList (zip vs (TGen1 <$> [0..]))

instantiate1 :: (MonadSupply Name1 m) => Scheme1 ([Name1], Name1) -> m (Type1 ([Name1], Name1))
instantiate1 (Forall1 _ ty) = do
    ts <- fmap yzz <$> supplies 5
    pure (replaceBound1 ts ty)

yzz :: Name1 -> Type1 ([Name1], Name1)
yzz n = TVar1 ([], n)

replaceBound1 :: [Type1 v] -> Type1 v -> Type1 v
replaceBound1 ts = \case
    TGen1 n     -> ts !! n
    TArr1 t1 t2 -> TArr1 (replaceBound1 ts t1) (replaceBound1 ts t2) 
    TApp1 t1 t2 -> TApp1 (replaceBound1 ts t1) (replaceBound1 ts t2) 
    TVar1 var   -> TVar1 var
    TCon1 con   -> TCon1 con

apply3 
  :: Map Name1 (Type1 Name1) 
  -> [Constraint1 ([Name1], Name1)] 
  -> [Constraint1 ([Name1], Name1)]
apply3 sub = fmap (apply4 sub)

apply4 
  :: Map Name1 (Type1 Name1) 
  -> Constraint1 ([Name1], Name1)
  -> Constraint1 ([Name1], Name1)
apply4 sub (Equality1 t1 t2)     = Equality1 (apply1 sub t1) (apply1 sub t2)
apply4 sub (Implicit1 t1 t2 set) = Implicit1 (apply1 sub t1) (apply1 sub t2) (apply5 sub set)
apply4 sub (Explicit1 t1 scheme) = Explicit1 (apply1 sub t1) (apply6 sub scheme)

apply5 
  :: Map Name1 (Type1 Name1) 
  -> Set Name1
  -> Set Name1
apply5 sub set = do
    a <- set
    free1 (apply2 sub (TVar1 a))

apply6 
  :: Map Name1 (Type1 Name1) 
  -> Scheme1 ([Name1], Name1)
  -> Scheme1 ([Name1], Name1)
apply6 sub (Forall1 ps t) = Forall1 ps (apply1 sub t)


---
---
---


expr101 :: Expr1 ()
expr101 = ELet1 () (PVar1 () "f") (EVar1 () "lenShow") (EVar1 () "f")

--expr102 = letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
--
--expr103 = lamExpr () (varPat () "x") (appExpr () [varExpr () "lenShow", varExpr () "x"])
--
--expr104 = lamExpr () (varPat () "x") (letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
--
--expr105 = letExpr () (varPat () "f") (varExpr () "lenShow") (lamExpr () (varPat () "x") (appExpr () [varExpr () "f", varExpr () "x"]))
--
--expr106 = appExpr () [varExpr () "lenShow", litExpr () (LInt 5)]


