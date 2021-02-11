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
import Control.Monad.Extra (allM, (||^))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Either.Combinators (rightToMaybe)
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
import Data.Tuple.Extra (fst3, snd3, thd3, third3)
import Data.Void
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Pretty
import Tau.Type
import Tau.Type.Substitution
import Tau.Type.Unification
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

--
--


frog e1 = foldr (\(a, b) e -> lamExpr (NodeInfo (tArr b (typeOf e1)) []) (varPat (NodeInfo b []) a) e) e1 

rebuildTree22 
  :: (MonadSupply Name m, MonadReader (ClassEnv (PatternExpr Type), TypeEnv, [Name]) m) -- (MonadError String m, MonadSupply Name m, MonadState Environments m) 
  => PatternExpr NodeInfo 
  -> StateT [(Name, Type)] m (PatternExpr NodeInfo)
rebuildTree22 a = do
    a <- xxx a
    xxxs <- get
    pure (frog a xxxs)
  where
    xxx = cata $ \case
        ELam t pat expr1 -> do
            let vars = free pat
            e1 <- local (third3 (Set.toList vars <>)) expr1
            pure (lamExpr t pat e1)

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            xxxs <- get
            put []
            e2 <- expr2
            pure (letExpr t pat (frog e1 xxxs) e2)

        EVar t var -> do
            -- 1. lambda bound var
            -- 2. let-bound variable
            -- 3. name

            let ds = nodePredicates t

            vars <- asks thd3

            if var `elem` vars
                then pure (varExpr t var)
                else foldrM funx (varExpr (stripNodePredicates t) var) ds

            --pure (varExpr t var)
            --pure (appExpr t [varExpr (stripNodePredicates t) var])

        e -> 
            embed <$> sequence e

funx :: (MonadSupply Name m, MonadReader (ClassEnv (PatternExpr Type), TypeEnv, [Name]) m) => Predicate -> PatternExpr NodeInfo -> StateT [(Name, Type)] m (PatternExpr NodeInfo)
funx (InClass name ty) expr = do
    env <- asks fst3
    if isVar ty 
        then do
            tv <- Text.replace "a" "&" <$> supply
            let t = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
                dict = varExpr (NodeInfo t []) tv
            --tell [(tv, t)]
            modify ((tv, t) :)
            pure (appExpr (exprTag expr) [expr, dict])
        else 
            case lookupClassInstance name ty env of
                Nothing -> 
                    error "missing class instance" -- throwError "baaaah"

                Just (a, Instance{..}) -> 
                    pure (appExpr (exprTag expr) [expr, mapTags (`NodeInfo` []) instanceDict])

joinDicts :: PatternExpr Type -> PatternExpr Type -> PatternExpr Type
joinDicts d1 d2 =
    case (project d1, project d2) of
        (ERec _ fields1, ERec t fields2) ->
            recExpr t (fields1 <> fields2)
        _ -> d2 -- error !!

buildDict 
  :: (MonadError String m, MonadSupply Name m, MonadState Environments m) 
  => Name 
  -> Type 
  -> ClassEnv a
  -> m (PatternExpr Type)
buildDict name ty env =
    case lookupClassInstance name ty env of
        Nothing -> throwError "bananas"
        Just (super, i@Instance{..}) -> do
            undefined
            --zzz <- traverse foo instancePredicates
            --yyy <- traverse boo super
            --pure (foldr1 joinDicts (instanceDict:zzz <> yyy))
  where
--    foo 
--      :: (MonadError String m, MonadSupply Name m, MonadState Environments m) 
--      => Predicate 
--      -> m a
    foo (InClass name1 ty1) = buildDict name1 ty1 env

    boo name2 = buildDict name2 ty env

rebuildTree 
  :: (MonadError String m, MonadSupply Name m, MonadState Environments m) 
  => PatternExpr NodeInfo 
  -> ReaderT Bool m (PatternExpr NodeInfo)
rebuildTree =
    cata $ \case
        EApp t exs -> do
            sequence exs >>= \case
                [] -> pure (appExpr t [])
                (e:es) -> do
                    let NodeInfo{..} = exprTag e 
                    ds <- traverse dict (sort nodePredicates)
                    pure (stripExprPredicates (appExpr t (e:ds <> (stripExprPredicates <$> es))))
                  where
                    dict 
                      :: (MonadError String m, MonadSupply Name m, MonadState Environments m) 
                      => Predicate 
                      -> m (PatternExpr NodeInfo)
                    dict (InClass name ty) = do
                        env <- gets classEnv
                        xx <- buildDict name ty env
                        traceShowM (pretty xx)
                        traceShowM ".^^."
                        pure (mapTags (`NodeInfo` []) xx)
                        --gets classEnv >>= \e -> 
                        --    case buildDict name ty e of
                        --        Nothing -> error ("Missing class instance: " <> Text.unpack (name <> " " <> prettyPrint ty))
                        --        Just e  -> do
                        --            traceShowM $ pretty e
                        --            traceShowM "...."
                        --            pure (mapTags (`NodeInfo` []) e)

                    stripExprPredicates = updateExprTag stripNodePredicates

        ELam t@NodeInfo{..} pat e1 -> do
           nested <- ask
           if nested then 
               lamExpr t pat <$> local (const True) e1

           else do
               vs <- Text.replace "a" "&" <$$> supplies (length nodePredicates)
               let pairs = zip (sort nodePredicates) vs
               modifyClassEnv (flip (foldr insertInstance) pairs)
               e <- lamExpr t (stripPatternPredicates pat) <$> local (const True) e1
               fst <$> foldl extendLam (pure (e, [])) (reverse pairs)
            where
              stripPatternPredicates = updatePatternTag stripNodePredicates

              insertInstance (InClass name ty, var) = 
                  let t = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
                   in addClassInstance name ty (varExpr t var)

              extendLam pex (p@(InClass name ty), var) = do 
                  (e, ps) <- pex
                  let t  = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
                      e1 = varPat (NodeInfo t []) var
                  pure (lamExpr (exprTag e) e1 (updateExprTag (setNodePredicates ps) e), p:ps) 

        e -> 
            embed <$> local (const False) (sequence e)


--

type ClassEnv a = Env (Class a)

super :: ClassEnv a -> Name -> [Name]
super env name = maybe [] fst (Env.lookup name env)

instances :: ClassEnv a -> Name -> [Instance a]
instances env name = maybe [] snd (Env.lookup name env)

addClassInstance :: Name -> Type -> a -> ClassEnv a -> ClassEnv a
addClassInstance name ty ex =
    Env.insertWith (const (second (inst :))) name ([], [inst]) 
  where
    inst = Instance [] ty ex

--type Class a = ([Name], [Instance a])
--gork :: Class a -> ([Name], Instance a)
--gork (super, insts) = undefined
--  where
--    abc = find ((ty ==) . instanceType) (instances env name)

lookupClassInstance :: Name -> Type -> ClassEnv a -> Maybe ([Name], Instance a)
lookupClassInstance name ty env = do -- undefined -- find ((ty ==) . instanceType) (instances env name)
    (super, instances) <- Env.lookup name env
    instance_ <- find ((ty ==) . instanceType) instances
    pure (super, instance_)

--lookupClassInstance :: Name -> Type -> ClassEnv a -> Maybe a
--lookupClassInstance name ty env =
--    undefined
----    instanceDict <$> listToMaybe boss
----  where
----    boss = filter ((ty ==) . instanceType) (instances env name)

--

bySuper :: ClassEnv a -> Predicate -> [Predicate]
bySuper env self@(InClass name ty) = 
    self:concat [bySuper env (InClass tc ty) | tc <- super env name]

byInstance :: ClassEnv a -> Predicate -> Maybe [Predicate]
byInstance env self@(InClass name ty) = 
    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
  where
    tryInstance :: Instance a -> Either String [Predicate]
    tryInstance (Instance ps h _) = 
        apply <$> matchClass (InClass name h) self <*> pure ps

--instance Substitutable Predicate where
--    apply sub (InClass name ty) = InClass name (apply sub ty)

entail :: ClassEnv a -> [Predicate] -> Predicate -> Either a Bool
entail env cls0 cl = pure super ||^ instances
  where
    super = any (cl `elem`) (bySuper env <$> cls0)
    instances = case byInstance env cl of
        Nothing   -> pure False
        Just cls1 -> allM (entail env cls0) cls1

isHeadNormalForm :: Predicate -> Bool
isHeadNormalForm (InClass _ t) = 
    flip cata t $ \case
        TApp t1 _ -> t1
        TVar{}    -> True
        _         -> False

toHeadNormalForm :: ClassEnv a -> [Predicate] -> Either a [Predicate]
toHeadNormalForm env = fmap concat . mapM (hnf env) 
  where
    hnf env tycl 
        | isHeadNormalForm tycl = pure [tycl]
        | otherwise = case byInstance env tycl of
            Nothing  -> error "ContextReductionFailed" -- throwError ContextReductionFailed Just cls -> toHeadNormalForm env cls


-- remove a class constraint if it is entailed by the other constraints in the list
simplify :: ClassEnv a -> [Predicate] -> Either a [Predicate]
simplify env = loop [] where
    loop qs [] = pure qs
    loop qs (p:ps) = do
        entailed <- entail env (qs <> ps) p
        if entailed then loop qs ps 
             else loop (p:qs) ps

reduce :: ClassEnv a -> [Predicate] -> Either a [Predicate]
reduce env cls = toHeadNormalForm env cls >>= simplify env 



unifyClass, matchClass :: (MonadError String m) => Predicate -> Predicate -> m Substitution
unifyClass = liftX unify
matchClass = liftX match

liftX :: (MonadError String m) => (Type -> Type -> m a) -> Predicate -> Predicate -> m a
liftX m (InClass c1 t1) (InClass c2 t2)
    | c1 == c2  = m t1 t2
    | otherwise = throwError "ClassMismatch" -- throwError ClassMismatch



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

setNodeType :: Type -> NodeInfo -> NodeInfo
setNodeType ty info = info{ nodeType = ty }

setNodePredicates :: [Predicate] -> NodeInfo -> NodeInfo
setNodePredicates ps info = info{ nodePredicates = ps }

stripNodePredicates :: NodeInfo -> NodeInfo
stripNodePredicates = setNodePredicates []


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

    copy k v e = fromMaybe e (Env.copy k <$> getTypeVar v <*> pure e)

lookupScheme 
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Name 
  -> StateT (Substitution, Env [Predicate]) m Scheme
lookupScheme name = do
    env <- asks snd 
    case Env.lookup name env of
        Nothing     -> throwError ("!! Unbound identifier: " <> Text.unpack name)
--        Just scheme -> pure scheme
        Just scheme -> gets (apply . fst) <*> pure scheme

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
    pure (concat [Env.findWithDefault [] v env | v <- vars])

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
            EOp  _ (OEq  a b) -> inferBinOp "(==)" OEq a b

            EOp  _ _ -> undefined

            EMat _ exs eqs -> do
                es1 <- sequence exs
                es2 <- sequence (inferClause newTy es1 <$> eqs)
                pure (matExpr (NodeInfo newTy []) es1 es2)

            ERec _ fields -> do
                let (_, ns, fs) = unzip3 (fieldsInfo fields)
                    info f = setFieldTag (NodeInfo (typeOf (fieldValue f)) []) f
                es <- sequence fs
                unifyTyped newTy (foldl tApp (recordConstructor ns) (typeOf <$> es))
                pure (recExpr (NodeInfo newTy []) (zipWith (info <$$> Field ()) ns es))

inferClause
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type
  -> [PatternExpr NodeInfo]
  -> Clause (Pattern t) (StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)) 
  -> StateT (Substitution, Env [Predicate]) m (Clause (Pattern NodeInfo) (PatternExpr NodeInfo))
inferClause ty exprs1 clause@(Clause ps _ _) = do
    (tps, vs) <- runWriterT (traverse inferPattern ps)
    let Clause _ exs e = local (second (Env.inserts (toScheme <$$> vs))) <$> clause
    forM_ exs (>>= unifyTyped tBool . typeOf)
    forM_ (zip tps exprs1) (\(p, e2) -> unifyTyped (typeOf p) (typeOf e2)) 
    e >>= unifyTyped ty . typeOf
    Clause tps <$> sequence exs <*> e

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
    (newTy, e1, e2) <- operands a b 
    unifyTyped newTy tBool
    unifyTyped e1 tBool
    unifyTyped e2 tBool
    pure (opExpr (NodeInfo newTy []) (op e1 e2))

inferBinOp
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Name
  -> (PatternExpr NodeInfo -> PatternExpr NodeInfo -> Op (PatternExpr NodeInfo))
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
  -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
inferBinOp name op a b = do
    (newTy, e1, e2) <- operands a b 
    (ty, ps) <- lookupScheme name >>= instantiate
    unifyTyped (typeOf e1 `tArr` typeOf e2 `tArr` newTy) ty 
    pure (opExpr (NodeInfo newTy ps) (op e1 e2))

operands
  :: (MonadSupply Name m, MonadReader (ClassEnv c, TypeEnv) m, MonadError String m) 
  => m a 
  -> m b
  -> m (TypeT v, a, b)
operands a b = do
    newTy <- newTVar kTyp
    e1 <- a
    e2 <- b
    pure (newTy, e1, e2)

type Infer s a = StateT (SubstitutionT s, Env [Predicate]) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv a -> TypeEnv -> Infer (TypeT s) a -> Either String (a, (SubstitutionT (TypeT s), Env [Predicate]))
runInfer e1 e2 = 
    flip runStateT mempty
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "error")
