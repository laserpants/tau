{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE FlexibleInstances     #-}
module Tau.Stuff where

import Control.Arrow ((>>>), (<<<), first, second)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Foldable (foldrM, traverse_)
import Data.Function ((&))
import Data.List
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Tree
import Data.Tree.View (showTree)
import Data.Tuple.Extra (snd3, third3)
import Data.Void
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Expr.Main
import Tau.Pretty
import Tau.Type
import Tau.Type.Main
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env


class Free t where
    free :: t -> Set Name

instance Free (TypeT a) where
    free = cata $ \case
        TVar _ var     -> Set.singleton var
        TArr t1 t2     -> t1 `Set.union` t2
        TApp t1 t2     -> t1 `Set.union` t2
        ty             -> mempty

--
-- Unification
--

bind :: (MonadError String m) => Name -> Kind -> Type -> m Substitution
bind name kind ty
    | ty == tVar kind name   = pure mempty
    | name `elem` free ty    = throwError "InfiniteType" -- throwError InfiniteType
    | Just kind /= kindOf ty = throwError "KindMismatch" -- throwError KindMismatch
    | otherwise              = pure (name `mapsTo` ty)

unify :: (MonadError String m) => Type -> Type -> m Substitution
unify t u = when (project t) (project u) where
    when (TArr t1 t2) (TArr u1 u2) = unifyPairs (t1, t2) (u1, u2)
    when (TApp t1 t2) (TApp u1 u2) = unifyPairs (t1, t2) (u1, u2)
    when (TVar kind name) _        = bind name kind u
    when _ (TVar kind name)        = bind name kind t
    when _ _ | t == u              = pure mempty
    when _ _                       = throwError "CannotUnify" -- throwError CannotUnify

unifyPairs :: (MonadError String m) => (Type, Type) -> (Type, Type) -> m Substitution
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

match :: (MonadError String m) => Type -> Type -> m Substitution
match t u = when (project t) (project u) where
    when (TArr t1 t2) (TArr u1 u2)            = matchPairs (t1, t2) (u1, u2)
    when (TApp t1 t2) (TApp u1 u2)            = matchPairs (t1, t2) (u1, u2)
    when (TVar k name) _ | Just k == kindOf u = pure (name `mapsTo` u)
    when _ _ | t == u                         = pure mempty
    when _ _                                  = throwError "CannotMatch" -- throwError CannotMatch

matchPairs :: (MonadError String m) => (Type, Type) -> (Type, Type) -> m Substitution
matchPairs (t1, t2) (u1, u2) = do
    sub1 <- match t1 u1
    sub2 <- match t2 u2
    case merge sub1 sub2 of
        Nothing  -> throwError "MergeFailed" -- throwError MergeFailed
        Just sub -> pure sub

--
-- Substitution
--

class Substitutable t a where
    apply :: SubstitutionT a -> t -> t

instance Substitutable t a => Substitutable [t] a where
    apply = fmap . apply

instance Substitutable (TypeT a) a where
    apply sub = cata $ \case
        TVar kind var -> subWithDefault (tVar kind var) var sub
        TArr t1 t2    -> tArr t1 t2
        TApp t1 t2    -> tApp t1 t2
        ty            -> embed ty

instance Substitutable NodeInfo Void where
    apply sub (NodeInfo ty a) = NodeInfo (apply sub ty) a

instance Substitutable (PredicateT a) a where
    apply sub (InClass name ty) = InClass name (apply sub ty)

instance Substitutable Scheme Int where
    apply sub (Forall ks ps ty) = Forall ks (apply sub ps) (apply sub ty)

newtype SubstitutionT a = Sub { getSub :: Map Name (TypeT a) }
    deriving (Show, Eq)

type Substitution = SubstitutionT Void

instance Semigroup (SubstitutionT a) where
    (<>) = compose

instance Monoid (SubstitutionT a) where
    mempty = nullSub

nullSub :: SubstitutionT a
nullSub = Sub mempty

mapsTo :: Name -> TypeT a -> SubstitutionT a
mapsTo name val = Sub (Map.singleton name val)

fromList :: [(Name, TypeT a)] -> SubstitutionT a
fromList = Sub . Map.fromList

toList :: SubstitutionT a -> [(Name, TypeT a)]
toList = Map.toList . getSub

subWithDefault :: TypeT a -> Name -> SubstitutionT a -> TypeT a
subWithDefault d name = Map.findWithDefault d name . getSub

domain :: SubstitutionT a -> [Name]
domain (Sub sub) = Map.keys sub

compose :: SubstitutionT a -> SubstitutionT a -> SubstitutionT a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

merge :: (Eq a) => SubstitutionT a -> SubstitutionT a -> Maybe (SubstitutionT a)
merge s1 s2 
    | allEqual  = Just (Sub (getSub s1 `Map.union` getSub s2))
    | otherwise = Nothing
  where
    allEqual = all equal (domain s1 `intersect` domain s2)

    equal :: Name -> Bool
    equal v = let app = (`apply` tVar kTyp v) :: (Eq a) => SubstitutionT a -> TypeT a
               in app s1 == app s2

unifyTypes 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadError String m
     , TypeOf s
     , TypeOf t ) 
  => s
  -> t
  -> StateT (Substitution, Env [Predicate]) m ()
unifyTypes v1 v2 = do 
    sub1 <- gets fst
    sub2 <- unify (apply sub1 t1) (apply sub1 t2)
    modify (first (sub2 <>))
    modify (second (Env.map (apply sub2) >>> propagateClasses sub2))
  where
    t1 = typeOf v1
    t2 = typeOf v2

    propagateClasses :: Substitution -> Env [Predicate] -> Env [Predicate]
    propagateClasses sub env = do
        Map.foldrWithKey fun env (getSub sub)

    fun k v e = 
        fromMaybe e (Env.copyKey k <$> getTypeVar v <*> pure e)

insertAssumption :: Name -> Scheme -> Env Scheme -> Env Scheme
insertAssumption = Env.insert

insertAssumptions :: [(Name, Scheme)] -> Env Scheme -> Env Scheme
insertAssumptions = flip (foldr (uncurry insertAssumption))

--
-- Type checker
--

type ClassEnv a = [a] -- TODO!!

data NodeInfo = NodeInfo 
    { nodeType       :: Type
    , nodePredicates :: [Predicate]
    } deriving (Show, Eq)

instance Pretty NodeInfo where
    pretty NodeInfo{..} = 
        case nodePredicates of
            []   -> pretty nodeType
            info -> pretty nodeType <+> pretty info

type TypeEnv = Env Scheme

newTVar :: (MonadSupply Name m) => Kind -> m (TypeT a)
newTVar kind = tVar kind <$> supply 

lookupScheme 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Name 
  -> m Scheme
lookupScheme name = do
    env <- asks snd 
    case Env.lookup name env of
        Nothing     -> throwError ("Unbound identifier: " <> Text.unpack name)
        Just scheme -> pure scheme

instantiate 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Scheme 
  -> StateT (Substitution, Env [Predicate]) m (Type, [Predicate])
instantiate (Forall kinds ps ty) = do
    tv <- supply
    ts <- traverse (\kind -> tVar kind <$> supply) kinds
    ns <- supplies (length ps)
    let newTy = tVar kTyp tv
        preds = replaceBoundInPredicate ts <$> ps
        zz = zip ns preds

    unifyTypes (replaceBound ts ty) (newTy :: Type)
    traverse_ foo zz
    sub <- gets fst
    pure (apply sub newTy, preds)
  where
    foo (t1, p@(InClass _ t2)) = do
        modify (second (Env.insert t1 [p]))
        unifyTypes (tVar kTyp t1 :: Type) t2

lookupPredicates 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => [Name]
  -> StateT (Substitution, Env [Predicate]) m [Predicate]
lookupPredicates vars = do
    env <- gets snd
    pure (concat [fromMaybe [] (Env.lookup v env) | v <- vars])

generalize
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type
  -> StateT (Substitution, Env [Predicate]) m Scheme
generalize ty = do
    set <- asks (Env.domain . snd)
    ps <- lookupPredicates (fst <$> vars)
    sub <- gets fst
    let qs = filter ((`notElem` set) . fst) vars
        sub = fromList [(fst v, tGen n) | (v, n) <- zip qs [0..]]
    pure (Forall (snd <$> qs) (apply sub . upgradePredicate <$> ps) (apply sub (upgrade ty)))
  where
    vars :: [(Name, Kind)]
    vars = nub . flip cata ty $ \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        ty         -> []

applySubAndGeneralize
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type
  -> StateT (Substitution, Env [Predicate]) m Scheme
applySubAndGeneralize ty = do
    sub <- gets fst
    generalize (apply sub ty)

class TypeOf a where
    typeOf :: a -> Type

instance TypeOf Type where
    typeOf = id

instance TypeOf (PatternExpr NodeInfo) where
    typeOf = nodeType . exprTag

instance TypeOf (Pattern NodeInfo) where
    typeOf = nodeType . patternTag

infer
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => PatternExpr t 
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
infer = cata alg
  where
    alg expr = do
        newTy <- newTVar kTyp
        case expr of
            EVar _ var -> do
                (ty, ps) <- lookupScheme var >>= instantiate
                unifyTypes ty newTy
                pure (varExpr (NodeInfo newTy ps) var)

            ECon _ con exprs -> do
                (ty, ps) <- lookupScheme con >>= instantiate
                es <- sequence exprs
                unifyTypes ty (foldr tArr newTy (typeOf <$> es))
                pure (conExpr (NodeInfo newTy ps) con es)

            ELit _ lit -> do
                ty <- inferLiteral lit
                unifyTypes newTy ty
                pure (litExpr (NodeInfo newTy []) lit)

            EApp _ exprs -> do
                es <- sequence exprs
                case es of
                    []     -> pure ()
                    f:args -> unifyTypes f (foldr tArr newTy (typeOf <$> args))
                pure (appExpr (NodeInfo newTy []) es)

            ELet _ pat expr1 expr2 -> do
                (tp, vs) <- runWriterT (inferPattern pat)
                e1 <- expr1
                unifyTypes (typeOf tp) (typeOf e1)
                ws <- traverse (secondM applySubAndGeneralize) vs 
                e2 <- local (second (insertAssumptions ws)) expr2
                unifyTypes newTy (typeOf e2)
                pure (letExpr (NodeInfo newTy []) tp e1 e2)

            ELam _ pat expr1 -> do
                (tp, vs) <- runWriterT (inferPattern pat)
                e1 <- local (second (insertAssumptions (fmap toScheme <$> vs))) expr1
                unifyTypes newTy (typeOf tp `tArr` typeOf e1)
                pure (lamExpr (NodeInfo newTy []) tp e1)

            EIf _ cond tr fl -> do
                e1 <- cond
                e2 <- tr
                e3 <- fl
                unifyTypes e1 tBool 
                unifyTypes e2 e3
                unifyTypes newTy e2
                pure (ifExpr (NodeInfo newTy []) e1 e2 e3)

            EOp  _ (OAnd a b) -> inferLogicOp OAnd a b
            EOp  _ (OOr  a b) -> inferLogicOp OOr a b
            EOp  _ _ -> undefined

            EMat _ exs eqs -> do
                undefined

            ERec _ fields -> do
                undefined

inferClause
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type
  -> [PatternExpr NodeInfo]
  -> Clause (Pattern t) (StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)) 
  -> StateT (Substitution, Env [Predicate]) m (Clause (Pattern Type) (PatternExpr Type))
inferClause =
    undefined

inferLiteral :: (MonadSupply Name m) => Literal -> StateT (Substitution, Env [Predicate]) m Type
inferLiteral = pure . \case
    LUnit{}    -> tUnit
    LBool{}    -> tBool
    LInt{}     -> tInt
    LInteger{} -> tInteger
    LFloat{}   -> tFloat
    LChar{}    -> tChar
    LString{}  -> tString

inferPattern
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Pattern t 
  -> WriterT [(Name, Type)] (StateT (Substitution, Env [Predicate]) m) (Pattern NodeInfo)
inferPattern = cata alg
  where
    alg pat = do
        newTy <- newTVar kTyp
        case pat of
            PVar _ var -> do
                tell [(var, newTy)]
                pure (varPat (NodeInfo newTy []) var)

            PCon _ con ps -> do
                (ty, qs) <- lift (lookupScheme con >>= instantiate)
                trs <- sequence ps
                lift (unifyTypes ty (foldr tArr newTy (typeOf <$> trs)))
                pure (conPat (NodeInfo newTy qs) con trs)

            PLit _ lit -> do
                ty <- lift (inferLiteral lit)
                pure (litPat (NodeInfo ty []) lit)

            PRec _ fields -> do
                let (_, ns, fs) = unzip3 (fieldsInfo fields)
                ps <- sequence fs
                let tfs = zipWith (\n p -> Field (patternTag p) n p) ns ps
                lift (unifyTypes newTy (foldl tApp (recordConstructor ns) (typeOf <$> ps)))
                pure (recPat (NodeInfo newTy []) tfs)

            PAny _ -> 
                pure (anyPat (NodeInfo newTy []))

inferLogicOp
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => (PatternExpr NodeInfo -> PatternExpr NodeInfo -> Op (PatternExpr NodeInfo))
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
inferLogicOp op a b = do
    newTy <- newTVar kTyp
    e1 <- a
    e2 <- b
    unifyTypes newTy tBool
    unifyTypes e1 tBool
    unifyTypes e2 tBool
    pure (opExpr (NodeInfo newTy []) (op e1 e2))

type Infer s a = StateT (SubstitutionT s, Env [Predicate]) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv a -> TypeEnv -> Infer s a -> Either String (a, (SubstitutionT s, Env [Predicate]))
runInfer e1 e2 = 
    flip runStateT mempty
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "error")
