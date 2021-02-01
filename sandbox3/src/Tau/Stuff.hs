{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TupleSections         #-}
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
import Data.Foldable (foldrM)
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
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env


class Free t where
    free :: t -> Set Name

instance Free (Type a) where
    free = cata $ \case
        TVar _ var     -> Set.singleton var
        TArr t1 t2     -> t1 `Set.union` t2
        TApp t1 t2     -> t1 `Set.union` t2
        ty             -> mempty

--
-- Unification
--

bind :: (MonadError String m) => Name -> Kind -> Type Void -> m (Substitution Void)
bind name kind ty
    | ty == tVar kind name   = pure mempty
    | name `elem` free ty    = throwError "InfiniteType" -- throwError InfiniteType
    | Just kind /= kindOf ty = throwError "KindMismatch" -- throwError KindMismatch
    | otherwise              = pure (name `mapsTo` ty)

unify :: (MonadError String m) => Type Void -> Type Void -> m (Substitution Void)
unify t u = when (project t) (project u) where
    when (TArr t1 t2) (TArr u1 u2) = unifyPairs (t1, t2) (u1, u2)
    when (TApp t1 t2) (TApp u1 u2) = unifyPairs (t1, t2) (u1, u2)
    when (TVar kind name) _        = bind name kind u
    when _ (TVar kind name)        = bind name kind t
    when _ _ | t == u              = pure mempty
    when _ _                       = throwError "CannotUnify" -- throwError CannotUnify

unifyPairs :: (MonadError String m) => (Type Void, Type Void) -> (Type Void, Type Void) -> m (Substitution Void)
unifyPairs (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

match :: (MonadError String m) => Type Void -> Type Void -> m (Substitution Void)
match t u = when (project t) (project u) where
    when (TArr t1 t2) (TArr u1 u2)            = matchPairs (t1, t2) (u1, u2)
    when (TApp t1 t2) (TApp u1 u2)            = matchPairs (t1, t2) (u1, u2)
    when (TVar k name) _ | Just k == kindOf u = pure (name `mapsTo` u)
    when _ _ | t == u                         = pure mempty
    when _ _                                  = throwError "CannotMatch" -- throwError CannotMatch

matchPairs :: (MonadError String m) => (Type Void, Type Void) -> (Type Void, Type Void) -> m (Substitution Void)
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
    apply :: Substitution a -> t -> t

instance Substitutable (Type a) a where
    apply sub = cata $ \case
        TVar kind var -> subWithDefault (tVar kind var) var sub
        TArr t1 t2    -> tArr t1 t2
        TApp t1 t2    -> tApp t1 t2
        ty            -> embed ty

instance Substitutable Scheme Int where
    apply sub = cata $ \case
        Forall k n cs s -> forall k n cs s
        Scheme t        -> scheme (apply sub t)

instance Substitutable NodeInfo Void where
    apply sub (NodeInfo ty a) = NodeInfo (apply sub ty) a

newtype Substitution a = Sub { getSub :: Map Name (Type a) }
    deriving (Show, Eq)

instance Semigroup (Substitution a) where
    (<>) = compose

instance Monoid (Substitution a) where
    mempty = nullSub

nullSub :: Substitution a
nullSub = Sub mempty

mapsTo :: Name -> Type a -> Substitution a
mapsTo name val = Sub (Map.singleton name val)

fromList :: [(Name, Type a)] -> Substitution a
fromList = Sub . Map.fromList

toList :: Substitution a -> [(Name, Type a)]
toList = Map.toList . getSub

subWithDefault :: Type a -> Name -> Substitution a -> Type a
subWithDefault d name = Map.findWithDefault d name . getSub

domain :: Substitution a -> [Name]
domain (Sub sub) = Map.keys sub

compose :: Substitution a -> Substitution a -> Substitution a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

merge :: (Eq a) => Substitution a -> Substitution a -> Maybe (Substitution a)
merge s1 s2 
    | allEqual  = Just (Sub (getSub s1 `Map.union` getSub s2))
    | otherwise = Nothing
  where
    allEqual = all equal (domain s1 `intersect` domain s2)

    equal :: Name -> Bool
    equal v = let app = (`apply` tVar kTyp v) :: (Eq a) => Substitution a -> Type a
               in app s1 == app s2

unifyTypes 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadError String m
     , TypeOf s
     , TypeOf t ) 
  => s
  -> t
  -> StateT (Substitution Void, Env [Predicate]) m ()
unifyTypes v1 v2 = do 
    sub1 <- gets fst
    sub2 <- unify (apply sub1 t1) (apply sub1 t2)
    modify (first (sub2 <>))
  where
    t1 = typeOf v1
    t2 = typeOf v2

insertAssumption :: Name -> Scheme -> Env Scheme -> Env Scheme
insertAssumption = Env.insert

insertAssumptions :: [(Name, Scheme)] -> Env Scheme -> Env Scheme
insertAssumptions = flip (foldr (uncurry insertAssumption))

--
-- Type checker
--

data Predicate = InClass Name (Type Void)
    deriving (Show, Eq, Ord)

-- TODO: Move to Tau.Pretty
instance Pretty Predicate where
    pretty (InClass name ty) = pretty name <+> pretty ty

type ClassEnv a = [a] -- TODO!!

data NodeInfo = NodeInfo 
    { nodeType       :: Type Void
    , nodePredicates :: [Predicate]
    } deriving (Show, Eq)

instance Pretty NodeInfo where
    pretty NodeInfo{..} = 
        case nodePredicates of
            []   -> pretty nodeType
            info -> pretty nodeType <+> pretty info

type TypeEnv = Env Scheme

newTVar :: (MonadSupply Name m) => Kind -> m (Type a)
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
  :: (MonadSupply Name m) 
  => Scheme 
  -> StateT (Substitution a, Env [Predicate]) m (Type Void)
instantiate scheme = do
    ps <- reverse <$> traverse (\kind -> (kind, ) <$> supply) kinds
    let ts = uncurry tVar <$> ps
    pure (replaceBound ts ty)
  where
    (ty, kinds) = flip cata scheme $ \case
        Scheme t             -> (t, [])
        Forall k _ _ (t, ks) -> (t, k:ks)

    replaceBound :: [Type Void] -> Type Int -> Type Void
    replaceBound ts = cata $ \case
        TGen n     -> ts !! n
        TArr t1 t2 -> tArr t1 t2
        TApp t1 t2 -> tApp t1 t2
        TVar k var -> tVar k var
        TCon k con -> tCon k con

generalize
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type Void
  -> StateT (Substitution Void, Env [Predicate]) m Scheme
generalize ty = do
    set <- asks (Env.domain . snd)
    let qs = filter ((`notElem` set) . fst) vars
        (ty1, sub, _) = foldr go (scheme_ ty, mempty, 0) qs
    pure (apply sub ty1)
  where
    names = reverse (take (length vars) (nameSupply ""))

    go (var, kind) (t, sub, n) = 
        ( forall kind (names !! n) [] t
        , var `mapsTo` tGen n <> sub
        , succ n )

    vars :: [(Name, Kind)]
    vars = nub . flip cata ty $ \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        ty         -> []

applySubAndGeneralize
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type Void
  -> StateT (Substitution Void, Env [Predicate]) m Scheme
applySubAndGeneralize ty = do
    sub <- gets fst
    generalize (apply sub ty)

class TypeOf a where
    typeOf :: a -> Type Void

instance TypeOf (Type Void) where
    typeOf = id

instance TypeOf (PatternExpr NodeInfo) where
    typeOf = nodeType . exprTag

instance TypeOf (Pattern NodeInfo) where
    typeOf = nodeType . patternTag

infer
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => PatternExpr t 
  -> StateT (Substitution Void, Env [Predicate]) m (PatternExpr NodeInfo)
infer = cata alg
  where
    alg expr = do
        newTy <- newTVar kTyp
        case expr of
            EVar _ var -> do
                ty <- lookupScheme var >>= instantiate
                unifyTypes ty newTy
                pure (varExpr (NodeInfo newTy []) var)

            ECon _ con exprs -> do
                ty <- lookupScheme con >>= instantiate
                es <- sequence exprs
                unifyTypes ty (foldr tArr newTy (typeOf <$> es))
                pure (conExpr (NodeInfo newTy []) con es)

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
                e1 <- local (second (insertAssumptions (fmap scheme_ <$> vs))) expr1
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
  => Type Void
  -> [PatternExpr NodeInfo]
  -> Clause (Pattern t) (StateT (Substitution Void, Env [Predicate]) m (PatternExpr NodeInfo)) 
  -> StateT (Substitution Void, Env [Predicate]) m (Clause (Pattern (Type Void)) (PatternExpr (Type Void)))
inferClause =
    undefined

inferLiteral :: (MonadSupply Name m) => Literal -> StateT (Substitution Void, Env [Predicate]) m (Type Void)
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
  -> WriterT [(Name, Type Void)] (StateT (Substitution Void, Env [Predicate]) m) (Pattern NodeInfo)
inferPattern = cata alg
  where
    alg pat = do
        newTy <- newTVar kTyp
        case pat of
            PVar _ var -> do
                tell [(var, newTy)]
                pure (varPat (NodeInfo newTy []) var)

            PCon _ con ps -> do
                ty <- lift (lookupScheme con >>= instantiate)
                trs <- sequence ps
                lift (unifyTypes ty (foldr tArr newTy (typeOf <$> trs)))
                pure (conPat (NodeInfo newTy []) con trs)

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
  -> StateT (Substitution Void, Env [Predicate]) m (PatternExpr NodeInfo)
  -> StateT (Substitution Void, Env [Predicate]) m (PatternExpr NodeInfo)
  -> StateT (Substitution Void, Env [Predicate]) m (PatternExpr NodeInfo)
inferLogicOp op a b = do
    newTy <- newTVar kTyp
    e1 <- a
    e2 <- b
    unifyTypes newTy tBool
    unifyTypes e1 tBool
    unifyTypes e2 tBool
    pure (opExpr (NodeInfo newTy []) (op e1 e2))

type Infer s a = StateT (Substitution s, Env [Predicate]) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv a -> TypeEnv -> Infer s a -> Either String (a, (Substitution s, Env [Predicate]))
runInfer e1 e2 = 
    flip runStateT mempty
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "error")
