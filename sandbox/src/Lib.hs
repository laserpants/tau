{-# LANGUAGE FlexibleContexts #-}
module Lib where

import Control.Monad.Reader
import Control.Monad.Supply
import Data.Foldable (foldlM)
import Data.List (nub, intersect)
import Data.Map.Strict (Map)
import Data.Set (Set, union)
import Data.Void
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type Name = String

newtype Env a = Env { getEnv :: Map Name a }
    deriving (Show, Eq)

--------------------------------

data Kind
    = KArr Kind Kind                 -- ^ Type-level function
    | Star                           -- ^ Concrete type
    deriving (Show, Eq)

data Type gen
    = TVar Name Kind                 -- ^ Type variable
    | TGen gen                       -- ^ Univ. quantified type variable
    | TCon Name Kind                 -- ^ Type constructor
    | TArr (Type gen) (Type gen)     -- ^ Function type
    | TApp (Type gen) (Type gen)     -- ^ Type application
    deriving (Show, Eq)

data ClassPred t = InClass Name t
    deriving (Show, Eq)

data Qualified t = [ClassPred t] :=> t
    deriving (Show, Eq)

data Scheme = Forall [Kind] (Qualified (Type Int))
    deriving (Show, Eq)

type Instance t = Qualified (ClassPred t)

type TyClass t = ([Name], [Instance t])

type ClassEnv g = (Env (TyClass (Type g)), [Type g])

--data Assumption t = Name :>: t
--    deriving (Show, Eq)
--
----------------------------------
--
--toScheme :: Type -> Scheme
--toScheme ty = Forall [] ([] :=> ty)
--
--tvar :: Name -> Kind -> Type
--tvar = TVar
--
--tcon :: Name -> Kind -> Type
--tcon = TCon
--
--tarr :: Type -> Type -> Type
--tarr = TArr
--
--infixr 1 `tarr`
--
--tapp :: Type -> Type -> Type
--tapp = TApp
--
--tUnit :: Type
--tUnit = tcon "Unit" Star
--
--tBool :: Type
--tBool = tcon "Bool" Star
--
--tInt :: Type
--tInt = tcon "Int" Star
--
--tListCon :: Type
--tListCon = tcon "List" (KArr Star Star)
--
--tList :: Type -> Type
--tList = tapp tListCon 
--
--
--kindOf :: Type -> Kind
--kindOf (TVar _ k) = k
--kindOf (TCon _ k) = k
--kindOf (TApp t _) = let KArr _ k = kindOf t in k
--kindOf TArr{}     = Star
--
--isHeadNormalForm :: ClassPred -> Bool
--isHeadNormalForm (InClass _ t) = hnf t
--  where
--    hnf :: Type -> Bool
--    hnf (TApp t _) = hnf t
--    hnf TVar{}     = True
--    hnf TGen{}     = True
--    hnf _          = False
--
--getVar :: Assumption t -> Name
--getVar (name :>: _) = name
--
--findAssumption :: Name -> [Assumption t] -> Maybe t
--findAssumption _ [] = Nothing 
--findAssumption i (name :>: a:as) = 
--    if i == name then Just a else findAssumption i as
--
--removeAssumption :: Name -> [Assumption t] -> [Assumption t]
--removeAssumption name = filter (\a -> name /= getVar a)
--
----------------------------------
--
--newtype Substitution = Subst { getSubst :: Map Name Type }
--    deriving (Show, Eq)
--
--substDom :: Substitution -> [Name]
--substDom (Subst sub) = Map.keys sub
--
--compose :: Substitution -> Substitution -> Substitution
--compose s1 s2 = Subst (fmap (apply s1) (getSubst s2) `Map.union` getSubst s1)
--
--merge :: Substitution -> Substitution -> Maybe Substitution
--merge s1 s2 = 
--    if all equal (substDom s1 `intersect` substDom s2)
--        then Just (Subst (getSubst s1 `Map.union` getSubst s2))
--        else Nothing
--  where
--    equal v = let app = (`apply` tvar v Star) in app s1 == app s2
--
--nullSubst :: Substitution
--nullSubst = Subst mempty
--
--mapsTo :: Name -> Type -> Substitution
--mapsTo name val = Subst (Map.singleton name val)
--
--substWithDefault :: Type -> Name -> Substitution -> Type
--substWithDefault def name = Map.findWithDefault def name . getSubst
--
--instance Semigroup Substitution where
--    (<>) = compose
--
--instance Monoid Substitution where
--    mempty = nullSubst
--
----------------------------------
--
--data Pattern
--    = PVar Name                      -- ^ Variable pattern
--    | PCon Name Scheme [Pattern]     -- ^ Constructor pattern
--    | PLit Literal                   -- ^ Literal pattern
--    | PAny                           -- ^ Wildcard pattern
--    deriving (Show, Eq)
--
--data Literal
--    = LUnit
--    | LBool Bool
--    | LInt Int
--    deriving (Show, Eq)
--
--data Expr
--    = EVar Name
--    | ELit Literal
--    | ECon Name Scheme
--    | EApp [Expr]
--    | ELet Pattern Expr Expr
--    | ELam Pattern Expr
--    deriving (Show, Eq)
--
----------------------------------
--
--evar :: Name -> Expr
--evar = EVar
--
--elit :: Literal -> Expr
--elit = ELit
--
--econ :: Name -> Scheme -> Expr
--econ = ECon
--
--eapp :: [Expr] -> Expr
--eapp = EApp
--
--elet :: Pattern -> Expr -> Expr -> Expr
--elet = ELet
--
--elam :: Pattern -> Expr -> Expr
--elam = ELam
--
----------------------------------
----------------------------------
--
--class Typed t where
--    apply :: Substitution -> t -> t
--    free  :: t -> Set Name
--
--instance (Typed t) => Typed [t] where
--    apply = fmap . apply
--    free  = foldr (Set.union . free) mempty
--
--instance Typed Type where
--    apply sub (TVar var kind) = substWithDefault (tvar var kind) var sub
--    apply sub (TArr t1 t2) = tarr (apply sub t1) (apply sub t2)
--    apply sub (TApp t1 t2) = tapp (apply sub t1) (apply sub t2)
--    apply _ ty = ty
--
--    free (TVar var _) = Set.singleton var
--    free (TArr t1 t2) = free t1 `union` free t2
--    free (TApp t1 t2) = free t1 `union` free t2
--    free _ = mempty
--
--instance Typed ClassPred where
--    apply sub (InClass name ty) = InClass name (apply sub ty)
--    free (InClass _ ty) = free ty
--
--instance (Typed t) => Typed (Qualified t) where
--    apply sub (ps :=> t) = apply sub ps :=> apply sub t
--    free (ps :=> t) = free ps `union` free t
--
--instance Typed Scheme where
--    apply sub (Forall kinds qt) = Forall kinds (apply sub qt)
--    free (Forall kinds qt) = free qt
--
--instance (Typed t) => Typed (Assumption t) where
--    apply sub (name :>: t) = name :>: apply sub t
--    free (name :>: t) = free t
--
----------------------------------
--
--data Error
--    -- Unification errors
--    = CannotUnify
--    | InfiniteType
--    | KindMismatch
--    -- Matching errors
--    | CannotMerge
--    | CannotMatch
--    deriving (Show, Eq)
--
--bind :: (Monad m) => Type -> Type -> m Substitution
--bind (TVar name kind) ty
--    | ty == TVar name kind = pure mempty
--    | name `elem` free ty  = error "Infinite type"
--    | kind /= kindOf ty    = error "Kind mismatch"
--    | otherwise            = pure (name `mapsTo` ty)
--bind _ _ = error "bind: bad call"
--
--unify :: (Monad m) => Type -> Type -> m Substitution
--unify (TArr t1 t2) (TArr u1 u2) = unifyPairs (t1, t2) (u1, u2)
--unify (TApp t1 t2) (TApp u1 u2) = unifyPairs (t1, t2) (u1, u2)
--unify u@TVar{} t = bind u t
--unify t u@TVar{} = bind u t
--unify t u
--    | t == u    = pure mempty
--    | otherwise = error "Cannot unify"
--
--unifyPairs :: (Monad m) => (Type, Type) -> (Type, Type) -> m Substitution
--unifyPairs (t1, t2) (u1, u2) = do
--    sub1 <- unify t1 u1
--    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
--    pure (sub2 <> sub1)
--
--match :: (Monad m) => Type -> Type -> m Substitution
--match (TArr t1 t2) (TArr u1 u2) = matchPairs (t1, t2) (u1, u2)
--match (TApp t1 t2) (TApp u1 u2) = matchPairs (t1, t2) (u1, u2)
--match (TVar name k) t 
--    | k == kindOf t = pure (name `mapsTo` t)
--match t u 
--    | t == u    = pure mempty
--    | otherwise = error "Cannot match"
--
--matchPairs :: (Monad m) => (Type, Type) -> (Type, Type) -> m Substitution
--matchPairs (t1, t2) (u1, u2) = do
--    sub1 <- match t1 u1
--    sub2 <- match t2 u2
--    case merge sub1 sub2 of
--        Nothing  -> error "Cannot merge"
--        Just sub -> pure sub
--
--unifyPred, matchPred :: ClassPred -> ClassPred -> Maybe Substitution
--unifyPred = liftX unify
--matchPred = liftX match
--
--liftX :: (Monad m) => (Type -> Type -> m a) -> ClassPred -> ClassPred -> m a
--liftX m (InClass c1 t1) (InClass c2 t2)
--    | c1 == c2  = m t1 t2
--    | otherwise = error "Classes do not match"
--
----------------------------------
--
--testExpr1 :: Expr
--testExpr1 = 
--    elet (PVar "f") (elam (PVar "x") (eapp [evar "(+)", evar "x", eapp [evar "f", evar "x"]])) (evar "f")
--
--type Constraint = (Type, Type)
--
--fresh :: (MonadSupply Name m) => Kind -> m Type
--fresh kind = TVar <$> supply <*> pure kind
--
--type Instantiate m t = t -> m t
--
--instantiate :: (MonadSupply Name m) => Scheme -> m (Qualified Type)
--instantiate (Forall ks qt) = do
--    ts <- traverse fresh ks
--    runReaderT (instQualified qt) ts
--  where
--    instQualified :: (MonadReader [Type] m) => Instantiate m (Qualified Type)
--    instQualified (ps :=> t) = do
--        qs <- traverse instPredicate ps
--        u  <- instType t
--        pure (qs :=> u)
--
--    instPredicate :: (MonadReader [Type] m) => Instantiate m ClassPred
--    instPredicate (InClass c t) = InClass <$> pure c <*> instType t
--
--    instType :: (MonadReader [Type] m) => Instantiate m Type
--    instType (TGen n) = do
--        ts <- ask
--        pure (ts !! n)
--    instType (TArr t1 t2) = TArr <$> instType t1 <*> instType t2
--    instType (TApp t1 t2) = TApp <$> instType t1 <*> instType t2
--    instType t = pure t
--
--removeAssumptionSet :: [Assumption t] -> [Assumption t] -> [Assumption t]
--removeAssumptionSet ts = flip (foldr removeAssumption) (nub (getVar <$> ts))
--
--type TypeAssumption = Assumption (Qualified Type)
--
--infer :: (MonadSupply Name m) => ([TypeAssumption], [Constraint]) -> Expr -> m (Qualified Type, [TypeAssumption], [Constraint])
--infer (as, cs) expr =
--    case expr of
--        EVar var -> do
--            name <- supply
--            let t = [] :=> tvar name Star
--            pure (t, [var :>: t], [])
--
--        ELit LUnit   -> pure ([] :=> tInt, [], [])
--        ELit LBool{} -> pure ([] :=> tBool, [], [])
--        ELit LInt{}  -> pure ([] :=> tInt, [], [])
--
--        ECon name scheme -> do
--            t <- instantiate scheme
--            pure (t, [name :>: t], [])
--
--        EApp (e:es) ->
--            foldl inferApp (infer (as, cs) e) es
--
--        ELet pat e1 e2 -> do
--            ts <- inferPat pat
--            (t1, as1, cs1) <- infer (as, cs) e1
--            (t2, as2, cs2) <- infer (as <> as1, cs <> cs1) e2
--            pure ( t2
--                 , as <> removeAssumptionSet ts as1 <> removeAssumptionSet ts as2
--                 , cs <> cs1 <> cs2 -- <> [(s, t) | (v :>: s) <- ts, (w :>: t) <- as1 <> as2, v == w] 
--                 )
--
----        ELam pat expr -> do
----            name <- supply
----            let beta = tvar name Star
----            ts <- inferPat pat
----            (t1, as1, cs1) <- infer (as, cs) expr
----            pure ( beta `tarr` t1
----                 , as <> as1
----                 , cs <> cs1 <> [(s, t) | (v :>: s) <- ts, (w :>: t) <- as1, v == w] )
--
--inferPat :: (MonadSupply Name m) => Pattern -> m [Assumption t]
--inferPat = undefined
--
--inferApp :: (MonadSupply Name m) => m (Qualified Type, [TypeAssumption], [Constraint]) -> Expr -> m (Qualified Type, [TypeAssumption], [Constraint])
--inferApp fun arg = do
--    name <- supply
--    let t = tvar name Star
--    (t1, as1, cs1) <- fun
--    (t2, as2, cs2) <- infer (as1, cs1) arg
--    pure ( [] :=> t
--         , as1 <> as2
--         , cs1 <> cs2 -- <> [(t1, t2 `tarr` t)] )
--         )
