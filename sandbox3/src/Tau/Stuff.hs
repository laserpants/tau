{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
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
import Data.Maybe (fromMaybe, maybeToList, listToMaybe, fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Tree
import Data.Tree.View (showTree)
import Data.Tuple.Extra (snd3, third3)
import Data.Void
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Pretty
import Tau.Type
import Tau.Type.Unification
import Tau.Type.Substitution
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

data Environments = Environments
    { classEnv :: ClassEnv (PatternExpr Type)
    , typeEnv  :: TypeEnv
--    , progEnv  :: Env (Expr QualifiedType (Prep QualifiedType) Name)
    } deriving (Show, Eq)

modifyClassEnv :: (MonadState Environments m) => (ClassEnv (PatternExpr Type) -> ClassEnv (PatternExpr Type)) -> m ()
modifyClassEnv f = do
    a <- get 
    put (a{ classEnv = f (classEnv a) })

modifyTypeEnv :: (MonadState Environments m) => (TypeEnv -> TypeEnv) -> m ()
modifyTypeEnv f = do
    a <- get 
    put (a{ typeEnv = f (typeEnv a) })

--myEnvironments = Environments
--    { classEnv = myClassEnv
--    , typeEnv  = myTypeEnv
----    , progEnv  = mempty
--    }

insertDicts 
  :: Env [Predicate]
  -> PatternExpr NodeInfo 
  -> PatternExpr NodeInfo
insertDicts env = mapTags $ \info@NodeInfo{..} -> 
        info{ nodePredicates = nub (nodePredicates <> predicates nodeType) }
  where
    predicates :: Type -> [Predicate]
    predicates t = concat [ concat $ maybeToList (Env.lookup v env) | v <- Set.toList (free t) ]

stripNodePredicates t = t{ nodePredicates = [] }

stripExprPredicates =
    updateExprTag stripNodePredicates

stripPatternPredicates =
    updatePatternTag stripNodePredicates

rebuildTree 
  :: (MonadSupply Name m, MonadState Environments m) 
  => PatternExpr NodeInfo 
  -> ReaderT Bool m (PatternExpr NodeInfo)
rebuildTree =
    cata $ \case
        EApp t exs -> do
            sequence exs >>= \case
                [] -> pure (appExpr t [])
                (e:es) -> do
                    let NodeInfo{..} = exprTag e 
                    ds <- traverse fun (sort nodePredicates)
                    pure (stripExprPredicates (appExpr t (e:ds <> (stripExprPredicates <$> es))))
--                    pure (appExpr t (e:es))
                  where
                    fun :: (MonadState Environments m) => Predicate -> m (PatternExpr NodeInfo)
                    fun (InClass name ty) = 
                        gets classEnv >>= \e -> 
                            case lookupClassInstance name ty e of
                                Nothing -> error ("missing class instance: " <> Text.unpack (name <> " " <> prettyPrint ty))
                                Just e  -> pure (mapTags (`NodeInfo` []) e)

        ELam t@NodeInfo{..} pat e1 -> do
           nested <- ask
           if nested 
               then 
                   lamExpr t pat <$> local (const True) e1
               else do
                   vs <- Text.replace "a" "v" <$$> supplies (length nodePredicates)
                   let xxxs = zip (sort nodePredicates) vs

                   let zyx = flip (foldr (\i@(InClass name ty, x) -> addClassInstance name ty (fooo i))) xxxs
                   modifyClassEnv zyx

                   --(lamExpr t pat <$> local (const True) e1)

                   --traceShowM "vvv"
                   --traceShowM (sort nodePredicates)

                   asdf <- (lamExpr t (stripPatternPredicates pat) <$> local (const True) e1)

                   fst <$> foldl gork2 (pure (asdf, [])) (reverse xxxs)

                   --(pure (asdf))


        e -> 
            embed <$> local (const False) (sequence e)

gork2 
  :: (Monad m) 
  => ReaderT Bool m (PatternExpr NodeInfo, [Predicate]) 
  -> (Predicate, Name) 
  -> ReaderT Bool m (PatternExpr NodeInfo, [Predicate])
gork2 pexpr (p@(InClass name ty), v) = do 
    (e, ps) <- pexpr
    let e1 = lamExpr (exprTag e) (varPat (NodeInfo fooss []) v) (setExprTag (flopp e (ps)) e)
    pure (e1, p:ps) 
  where
    flopp e ps = (exprTag e){ nodePredicates = ps }

    fooss = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty

fooo :: (Predicate, Name) -> Expr Type p q
fooo (InClass name ty, var) = 
    varExpr (tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty) var

--

type Class a = ([Name], [Instance a])

data Instance a = Instance [Predicate] Type a
    deriving (Show, Eq)

instanceType :: Instance a -> Type
instanceType (Instance _ ty _) = ty

instanceX :: Instance a -> a
instanceX (Instance _ _ a) = a

type ClassEnv a = Env (Class a)

super :: ClassEnv a -> Name -> [Name]
super env name = maybe [] fst (Env.lookup name env)

instances :: ClassEnv a -> Name -> [Instance a]
instances env name = maybe [] snd (Env.lookup name env)

--type Class a = ([Name], [Instance a])

addClassInstance :: Name -> Type -> a -> ClassEnv a -> ClassEnv a
addClassInstance name ty ex =
    Env.insertWith (const (second (inst :))) name ([], [inst]) 
  where
    inst = Instance [] ty ex

lookupClassInstance :: Name -> Type -> ClassEnv a -> Maybe a
lookupClassInstance name ty env =
    instanceX <$> listToMaybe boss
  where
    boss = filter ((ty ==) . instanceType) (instances env name)

--
-- Type checker
--

data NodeInfo = NodeInfo 
    { nodeType       :: Type
    , nodePredicates :: [Predicate]
    } deriving (Show, Eq)

instance Substitutable NodeInfo Type where
    apply sub (NodeInfo ty ps) = NodeInfo (apply sub ty) (apply sub ps)

instance Pretty NodeInfo where
    pretty NodeInfo{..} = 
        case nodePredicates of
            []   -> pretty nodeType
            info -> pretty nodeType <+> pretty info

instance Typed NodeInfo where
    typeOf = nodeType

type TypeEnv = Env Scheme

--instance Substitutable TypeEnv Void where
--    apply sub = Env.map (apply sub)

instance Substitutable TypeEnv Type where
    apply sub = Env.map (apply sub)

instance Free TypeEnv where
    free = free . Env.elems

--

unified 
  :: (MonadError String m) 
  => Type 
  -> Type 
  -> StateT (Substitution, Env [Predicate]) m Substitution
unified t1 t2 = do
    sub1 <- gets fst
    sub2 <- unify (apply sub1 t1) (apply sub1 t2)
    pure (sub2 <> sub1)

unifyTyped 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv a, TypeEnv) m
     , MonadError String m
     , Typed s
     , Typed t ) 
  => s
  -> t
  -> StateT (Substitution, Env [Predicate]) m ()
unifyTyped v1 v2 = do 
    sub <- unified (typeOf v1) (typeOf v2)
    modify (first (sub <>))
    modify (second (Env.map (apply sub) >>> propagateClasses sub))
  where
    propagateClasses :: Substitution -> Env [Predicate] -> Env [Predicate]
    propagateClasses sub env = Map.foldrWithKey copy env (getSub sub)

    copy k v e = fromMaybe e (Env.copyKey k <$> getTypeVar v <*> pure e)

lookupScheme 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Name 
  -> StateT (Substitution, Env [Predicate]) m Scheme
lookupScheme name = do
    env <- asks snd 
    sub <- gets fst
    case Env.lookup name env of
        Nothing     -> throwError ("Unbound identifier: " <> Text.unpack name)
--        Just scheme -> pure scheme
        Just scheme -> gets fst >>= \sub -> pure (apply sub scheme)

instantiate 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Scheme 
  -> StateT (Substitution, Env [Predicate]) m (Type, [Predicate])
instantiate (Forall kinds ps ty) = do
    names <- supplies (length kinds)
    let ts = zipWith tVar kinds names 
        preds = fun <$> ps
        fun p@(InClass name n) = ( names !! n
                                 , replaceBound ts <$> (tGen <$> p) )
    modify (second (flip (foldr (uncurry (\k -> Env.insertWith (<>) k . pure))) preds))
    pure (replaceBound ts ty, snd <$> preds)

lookupPredicates 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => [Name]
  -> StateT (Substitution, Env [Predicate]) m [Predicate]
lookupPredicates vars = do
    env <- gets snd
    --let env = Env.fromList [("a4" :: Name, [InClass "Show" (tVar kTyp "a4")])]
    pure (concat [fromMaybe [] (Env.lookup v env) | v <- vars])

generalize
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type
  -> StateT (Substitution, Env [Predicate]) m Scheme
generalize ty = do
    env <- asks snd
    sub1 <- gets fst
    let ty1   = apply sub1 ty
        pairs = filter ((`notElem` free (apply sub1 env)) . fst) (typeVars ty1)
        sub2  = fromList [(fst v, tGen n) | (v, n) <- zip pairs [0..]]
        ty2   = apply sub2 (upgrade ty1)
    ps <- lookupPredicates (fst <$> pairs)
    pure (Forall (snd <$> pairs) 
                 (traverse (maybeToList . getTypeIndex) =<< apply sub2 
                 (upgrade <$$> ps)) ty2)
  where
    typeVars :: Type -> [(Name, Kind)]
    typeVars ty = nub . flip cata ty $ \case
        TVar k var -> [(var, k)]
        TArr t1 t2 -> t1 <> t2
        TApp t1 t2 -> t1 <> t2
        ty         -> []

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
                unifyTyped ty newTy
                pure (varExpr (NodeInfo newTy ps) var)

            ECon _ con exprs -> do
                (ty, ps) <- lookupScheme con >>= instantiate
                es <- sequence exprs
                unifyTyped ty (foldr tArr newTy (typeOf <$> es))
                pure (conExpr (NodeInfo newTy ps) con es)

            ELit _ lit -> do
                ty <- inferLiteral lit
                unifyTyped newTy ty
                pure (litExpr (NodeInfo newTy []) lit)

            EApp _ exprs -> do
                es <- sequence exprs
                case es of
                    []     -> pure ()
                    f:args -> unifyTyped f (foldr tArr newTy (typeOf <$> args))
                pure (appExpr (NodeInfo newTy []) es)

            ELet _ pat expr1 expr2 -> do
                (tp, vs) <- runWriterT (inferPattern pat)
                e1 <- expr1
                unifyTyped tp e1
                vs1 <- traverse (secondM generalize) vs
                e2 <- local (second (Env.inserts vs1)) expr2
                unifyTyped newTy e2
                pure (letExpr (NodeInfo newTy []) tp e1 e2)

            ELam _ pat expr1 -> do
                (tp, vs) <- runWriterT (inferPattern pat)
                e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
                unifyTyped newTy (typeOf tp `tArr` typeOf e1)
                pure (lamExpr (NodeInfo newTy []) tp e1)

            EIf _ cond tr fl -> do
                e1 <- cond
                e2 <- tr
                e3 <- fl
                unifyTyped e1 tBool 
                unifyTyped e2 e3
                unifyTyped newTy e2
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
                lift (unifyTyped ty (foldr tArr newTy (typeOf <$> trs)))
                pure (conPat (NodeInfo newTy qs) con trs)

            PLit _ lit -> do
                ty <- lift (inferLiteral lit)
                pure (litPat (NodeInfo ty []) lit)

            PRec _ fields -> do
                let (_, ns, fs) = unzip3 (fieldsInfo fields)
                ps <- sequence fs
                let tfs = zipWith (\n p -> Field (patternTag p) n p) ns ps
                lift (unifyTyped newTy (foldl tApp (recordConstructor ns) (typeOf <$> ps)))
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
    unifyTyped newTy tBool
    unifyTyped e1 tBool
    unifyTyped e2 tBool
    pure (opExpr (NodeInfo newTy []) (op e1 e2))

type Infer s a = StateT (SubstitutionT s, Env [Predicate]) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv a -> TypeEnv -> Infer (TypeT s) a -> Either String (a, (SubstitutionT (TypeT s), Env [Predicate]))
runInfer e1 e2 = 
    flip runStateT mempty
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "error")
