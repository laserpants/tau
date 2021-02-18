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
import Data.Tuple.Extra (fst3, snd3, thd3, third3, second3)
import Data.Void
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Pretty
import Tau.PrettyTree
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


frog e1 = foldr (\(a, b) e -> lamExpr (NodeInfo (tArr b (typeOf e1)) []) [varPat (NodeInfo b []) a] e) e1 

--stuffs :: (Monad m) => Pattern t -> m [(Name, Scheme)]
--stuffs = cata $ \case
--    PVar t var ->
--        pure [(var, nodeType t)]

rebuildTree22 
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (PatternExpr NodeInfo), TypeEnv, [Name]) m) -- (MonadError String m, MonadSupply Name m, MonadState Environments m) 
  => PatternExpr NodeInfo 
  -> StateT [(Name, Type)] m (PatternExpr NodeInfo)
rebuildTree22 a = do
    a <- xxx a
    xxxs <- nub <$> reset
    --traceShowM ":::::::::::"
    --traceShowM xxxs
    pure (frog a (nub xxxs))
  where
    xxx = cata $ \case
        --ELam t pat expr1 -> 
        --    -- TODO: I don't think we need to do this!!!??
        --    lamExpr t pat <$> local (third3 (Set.toList (free pat) <>)) expr1

        ELet t pat expr1 expr2 -> do
            e1 <- expr1
            xxxs <- nub <$> reset
            e2 <- expr2
            --vs <- stuffs pat
            ----e2 <- local (second (Env.inserts vs)) expr2
            --e2 <- local (second3 (Env.inserts vs)) expr2
            traceShowM xxxs
            pure (letExpr t pat (frog e1 (nub xxxs)) e2)

        EOp t (OAdd a b) -> do
            e1 <- a
            e2 <- b
            let t1 = nodeType t
            rebuildTree22 (appExpr t [varExpr (NodeInfo (t1 `tArr` t1 `tArr` t1) [InClass "Num" t1]) "(+)", e1, e2])

        EVar t var -> do
            -- 1. lambda bound var
            -- 2. let-bound variable
            -- 3. name

            let ds = nodePredicates t

            vars <- asks thd3

            --if var `elem` vars
            --    then pure (varExpr t var)
            --    else foldrM funx (varExpr (stripNodePredicates t) var) ds

            foldrM funx (varExpr (stripNodePredicates t) var) ds

            --pure (varExpr t var)
            --pure (appExpr t [varExpr (stripNodePredicates t) var])

        e -> 
            embed <$> sequence e

abcd (Fix (EVar t name)) = varExpr t ("." <> name)
abcd e = e

funx 
  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (PatternExpr NodeInfo), TypeEnv, [Name]) m) 
  => Predicate 
  -> PatternExpr NodeInfo 
  -> StateT [(Name, Type)] m (PatternExpr NodeInfo)
funx (InClass name ty) expr = do
    env <- asks fst3
    if isVar ty 
        then do
            tv <- Text.replace "a" "&" <$> supply
            let t = tApp (tCon (kArr kTyp (fromJust (kindOf ty))) name) ty
                dict = varExpr (NodeInfo t []) tv
            modify ((tv, t) :)
            pure (appExpr (exprTag expr) [expr, dict])
        else do
            --let baz = msum [tryInstance i | i <- Env.toList env]
            case lookupClassInstance name ty env of
                Nothing -> do
                    --traceShowM name
                    --traceShowM ty
                    --traceShowM env
                    error "mmissing class instance" -- throwError "baaaah"

                Just (a, i@Instance{..}) -> do
                    --traceShowM (pretty instanceDict)
--                    traceShowM "vvvvvvv"
--                    traceShowM "vvvvvvv"
--                    traceShowM "vvvvvvv"
--                    --undefined
--                    (debugTree instanceDict)


                    foo <- rebuildTree22 instanceDict
--                    traceShowM (pretty foo)
--                    traceShowM (pretty (typeOf foo))
--                    --env2 <- asks snd3
--                    --mapM_ traceShowM (Env.toList env2) -- (Env.lookup "showList" env2)
--                    traceShowM "^^^^^^^"
--                    traceShowM "^^^^^^^"
--                    traceShowM "^^^^^^^"
--
                    --let foo = instanceDict

                    --let zz:_ = a 
                    --let fork = [lookupClassInstance zz ty env | zz <- a]

                    --let dog = fork :: Int

                    --traceShowM fork

                    --[funx (InClass zzz ty) expr | zzz <- a]
                    --let zzz:_ = a
                    --hello <- funx (InClass zzz ty) expr
                    --traceShowM hello

                    --deps a (appExpr (exprTag expr) [expr, mapTags (`NodeInfo` []) instanceDict])

                    --pure (appExpr (exprTag expr) [expr, mapTags (`NodeInfo` []) instanceDict])
                    let ee = setExprTag (NodeInfo (typeOf foo `tArr` nodeType (exprTag expr)) []) expr

                    pure (appExpr (exprTag expr) [ee, foo])

                    --pure (letExpr (exprTag expr) (varPat (exprTag expr) "show") (varExpr (exprTag expr) "@showInt") (appExpr (exprTag expr) [expr, mapTags (`NodeInfo` []) instanceDict]))





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

lookupClassInstance :: Name -> Type -> ClassEnv (PatternExpr NodeInfo) -> Maybe ([Name], Instance (PatternExpr NodeInfo))
lookupClassInstance name ty env = do -- undefined -- find ((ty ==) . instanceType) (instances env name)
    (super, instances) <- Env.lookup name env
    msum [tryX i | i <- instances]
    --instance_ <- find ((ty ==) . instanceType) instances
    --pure undefined -- (super, instance_)
  where
--    tryX :: Instance a -> Maybe ([Name], Instance (PatternExpr NodeInfo))
    tryX ii@(Instance ps t d) = 
        case match t ty of
            Left _    -> Nothing
            --Right sub -> do
                --let ee = d :: PatternExpr NodeInfo
                --Just ([], undefined) -- apply sub t
            Right sub -> do
                debugTree d
                mapM_ traceShowM (Map.toList (getSub sub))
                Just ([], Instance (apply sub ps) (apply sub t) (mapTags (apply sub) d))


--lookupClassInstance :: Name -> Type -> ClassEnv a -> Maybe ([Name], Instance a)
--lookupClassInstance name ty env = do -- undefined -- find ((ty ==) . instanceType) (instances env name)
--    (super, instances) <- Env.lookup name env
--    instance_ <- find ((ty ==) . instanceType) instances
--    pure (super, instance_)

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
byInstance env self@(InClass name ty) = do
--    traceShowM self
    msum $ rightToMaybe <$> [tryInstance i | i <- instances env name]
  where
    tryInstance :: Instance a -> Either String [Predicate]
    tryInstance (Instance ps h _) = 
        -- TODO: use match???
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
            Nothing  -> error "ContextReductionFailed" -- throwError ContextReductionFailed 
            Just cls -> toHeadNormalForm env cls


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
     , Typed t
     , Typed u ) 
  => t
  -> u
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
        --ty2   = apply sub2 (upgrade ty1)
    ps <- lookupPredicates (fst <$> pairs)
    pure (Forall (snd <$> pairs) 
                 (traverse (maybeToList . getTypeIndex) =<< apply sub2 
                 --(upgrade <$$> ps)) ty2)
                 (upgrade <$$> ps)) (apply sub2 (upgrade ty1)))

infer
  :: (MonadFix m, MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
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

            EFix _ name expr1 expr2 -> do

                --let boss :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) => PatternExpr NodeInfo -> StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)
                --    boss pex = do 
                --            s <- generalize (typeOf pex)
                --            local (second (Env.insert name s)) (pure pex)

                --e1 <- mfix boss

                --e1 <- local (second (Env.insert name undefined)) expr1

                t1 <- newTVar kTyp
                e1 <- local (second (Env.insert name (toScheme t1))) expr1
                unifyTyped t1 e1
                s <- generalize (typeOf e1)
                e2 <- local (second (Env.insert name s)) expr2
                unifyTyped newTy e2
                pure (fixExpr (NodeInfo newTy []) name e1 e2)

            ELet _ pat expr1 expr2 -> do
                (tp, vs) <- runWriterT (inferPattern pat)
                e1 <- expr1
                unifyTyped tp e1
                vs1 <- traverse (secondM generalize) vs
                e2 <- local (second (Env.inserts vs1)) expr2
                unifyTyped newTy e2
                pure (letExpr (NodeInfo newTy []) tp e1 e2)

            --ELam _ pat expr1 -> do
            --    (tp, vs) <- runWriterT (inferPattern pat)
            --    e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
            --    unifyTyped newTy (typeOf tp `tArr` typeOf e1)
            --    pure (lamExpr (NodeInfo newTy []) tp e1)

            ELam _ pats expr1 -> do
                (tps, vs) <- runWriterT (traverse inferPattern pats)
                e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
                unifyTyped newTy (foldr tArr (typeOf e1) (typeOf <$> tps))
                pure (lamExpr (NodeInfo newTy []) tps e1)

            EIf _ cond tr fl -> do
                e1 <- cond
                e2 <- tr
                e3 <- fl
                unifyTyped e1 (tBool :: Type)
                unifyTyped e2 e3
                unifyTyped newTy e2
                pure (ifExpr (NodeInfo newTy []) e1 e2 e3)

            EOp  _ (OAnd a b) -> inferLogicOp OAnd a b
            EOp  _ (OOr  a b) -> inferLogicOp OOr a b
            EOp  _ (OEq  a b) -> inferBinOp "(==)" OEq a b
            EOp  _ (OAdd a b) -> inferBinOp "(+)"  OAdd a b

            EOp  _ (ODot name expr1) -> do
                e1 <- expr1
                (ty, ps) <- lookupScheme name >>= instantiate
                unifyTyped (typeOf e1 `tArr` newTy) ty
                pure (opExpr (NodeInfo newTy ps) (ODot name e1))

--            \xs => match [xs] with
--              | (x :: xs) => 0
            EPat _ [] eqs -> do
                t1 <- newTVar kTyp
                es2 <- sequence (inferClause newTy [t1] <$> eqs)
                pure (patExpr (NodeInfo (t1 `tArr` newTy) []) [] es2)

--            match xs with
--              | (x :: xs) => 0
            EPat _ exs eqs -> do
                es1 <- sequence exs
                es2 <- sequence (inferClause newTy (typeOf <$> es1) <$> eqs)
                pure (patExpr (NodeInfo newTy []) es1 es2)

            ERec _ fields -> do
                let (_, ns, fs) = unzip3 (fieldsInfo fields)
                    info f = setFieldTag (NodeInfo (typeOf (fieldValue f)) []) f
                es <- sequence fs
                unifyTyped newTy (tRecord ns (typeOf <$> es))
                pure (recExpr (NodeInfo newTy []) (zipWith (info <$$> Field ()) ns es))

inferClause
  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
  => Type
  -> [Type]
  -> Clause (Pattern t) (StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)) 
  -> StateT (Substitution, Env [Predicate]) m (Clause (Pattern NodeInfo) (PatternExpr NodeInfo))
inferClause ty types clause@(Clause ps _ _) = do
    (tps, vs) <- runWriterT (traverse inferPattern ps)
    let Clause _ exs e = local (second (Env.inserts (toScheme <$$> vs))) <$> clause
    forM_ exs (>>= unifyTyped (tBool :: Type) . typeOf)
    forM_ (zip tps types) (uncurry unifyTyped) 
    e >>= unifyTyped ty . typeOf
    Clause tps <$> sequence exs <*> e

--inferClause
--  :: (MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m, MonadError String m) 
--  => Type
--  -> [PatternExpr NodeInfo]
--  -> Clause (Pattern t) (StateT (Substitution, Env [Predicate]) m (PatternExpr NodeInfo)) 
--  -> StateT (Substitution, Env [Predicate]) m (Clause (Pattern NodeInfo) (PatternExpr NodeInfo))
--inferClause ty exprs1 clause@(Clause ps _ _) = do
--    (tps, vs) <- runWriterT (traverse inferPattern ps)
--    let Clause _ exs e = local (second (Env.inserts (toScheme <$$> vs))) <$> clause
--    forM_ exs (>>= unifyTyped (tBool :: Type) . typeOf)
--    forM_ (zip tps exprs1) (\(p, e2) -> unifyTyped (typeOf p) (typeOf e2)) 
--    e >>= unifyTyped ty . typeOf
--    Clause tps <$> sequence exs <*> e

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
                lift (unifyTyped newTy (tRecord ns (typeOf <$> ps)))
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
    unifyTyped newTy (tBool :: Type)
    unifyTyped e1 (tBool :: Type)
    unifyTyped e2 (tBool :: Type)
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
    traceShowM (pretty ty)
    traceShowM ps
    traceShowM "**"
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
