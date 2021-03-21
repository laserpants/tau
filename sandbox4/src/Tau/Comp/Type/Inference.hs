{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Comp.Type.Inference where

import Control.Arrow ((>>>), (***))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Either.Extra (maybeToEither, isLeft)
import Data.Maybe (fromMaybe, maybeToList, fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Tuple.Extra (first, second)
import Data.Void
import Tau.Comp.Type.Substitution
import Tau.Comp.Type.Unification
import Tau.Lang.Expr
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

data NodeInfoT t = NodeInfo
    { nodeType       :: t
    , nodePredicates :: [Predicate]
    } deriving (Show, Eq)

type NodeInfo = NodeInfoT Type

-- TODO: move
type ClassEnv f g c d = Env 
    ( ClassInfo Name Type
    , [ClassInfo Type (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) () () () ())] )

instance Substitutable NodeInfo Type where
    apply sub NodeInfo{..} = NodeInfo
        { nodeType       = apply sub nodeType
        , nodePredicates = apply sub nodePredicates }

instance (Free t) => Free (NodeInfoT t) where
    free = free . nodeType

instance (Typed t) => Typed (NodeInfoT t) where
    typeOf = typeOf . nodeType

instance (Typed t) => Typed (Ast t n o f g c d) where
    typeOf = typeOf . exprTag

instance (Typed t) => Typed (Pattern t f g) where
    typeOf = typeOf . patternTag

instance (Typed t) => Typed (Op1 t) where
    typeOf = typeOf . op1Tag

instance (Typed t) => Typed (Op2 t) where
    typeOf = typeOf . op2Tag

instance MapT NodeInfo t Void Void where
    mapTagsM = const pure

--instance MapT t t (NodeInfoT t) (NodeInfoT t) where
--    mapTagsM f (NodeInfo t ps) = NodeInfo <$> f t <*> pure ps

instance 
    ( MapT NodeInfo NodeInfo n n
    , MapT NodeInfo NodeInfo o o 
    ) => Substitutable (Ast NodeInfo n o f g c d) Type 
  where apply sub = mapTags (apply sub :: NodeInfo -> NodeInfo)

infer 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m )
  => Ast t (Op1 t) (Op2 t) f g c d
  -> m (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f g c d)
infer = cata $ \expr -> do
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
            ty <- inferPrim lit
            unifyTyped newTy ty
            pure (litExpr (NodeInfo newTy []) lit)

        EApp _ exprs -> do
            es <- sequence exprs
            case es of
                []     -> pure ()
                f:args -> unifyTyped f (foldr tArr newTy (typeOf <$> args))
            pure (appExpr (NodeInfo newTy []) es)

        ELet _ (BLet pat) expr1 expr2 -> do
            (tp, vs) <- runWriterT (inferPattern pat)
            e1 <- expr1
            unifyTyped tp e1
            vs1 <- traverse (secondM generalize) vs
            e2 <- local (second (Env.inserts vs1)) expr2
            unifyTyped newTy e2
            pure (letExpr (NodeInfo newTy []) (BLet tp) e1 e2)

        ELet _ (BFun f pats) expr1 expr2 -> do
            (tps, vs) <- runWriterT (traverse inferPattern pats)
            e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
            t1 <- newTVar kTyp
            unifyTyped t1 (foldr tArr (typeOf e1) (typeOf <$> tps))
            scheme <- generalize t1
            e2 <- local (second (Env.insert f scheme)) expr2
            unifyTyped newTy e2
            pure (letExpr (NodeInfo newTy []) (BFun f tps) e1 e2)

        EFix _ name expr1 expr2 -> do
            t1 <- newTVar kTyp
            e1 <- local (second (Env.insert name (toScheme t1))) expr1
            unifyTyped t1 e1
            scheme <- generalize (typeOf e1)
            e2 <- local (second (Env.insert name scheme)) expr2
            unifyTyped newTy e2
            pure (fixExpr (NodeInfo newTy []) name e1 e2)

        ELam _ pats expr1 -> do            
            (tps, vs) <- runWriterT (traverse inferPattern pats)
            e1 <- local (second (Env.inserts (toScheme <$$> vs))) expr1
            unifyTyped newTy (foldr tArr (typeOf e1) (typeOf <$> tps))
            pure (lamExpr (NodeInfo newTy []) tps e1)

        EIf  _ cond tr fl -> do
            e1 <- cond
            e2 <- tr
            e3 <- fl
            unifyTyped e1 (tBool :: Type)
            unifyTyped e2 e3
            unifyTyped newTy e2
            pure (ifExpr (NodeInfo newTy []) e1 e2 e3)

        --
        -- fun-expression, e.g.,
        --
        --    fun 
        --      | Some a => a
        --      | None   => 0
        --
        EPat _ [] eqs@(Clause ps _ _:_) -> do
            ts <- tVar kTyp <$$> supplies (length ps)
            es2 <- sequence (inferClause newTy ts <$> eqs)
            pure (patExpr (NodeInfo (foldr tArr newTy ts) []) [] es2)

        --
        -- Ordinary match expression
        --
        EPat _ exs eqs -> do
            es1 <- sequence exs
            es2 <- sequence (inferClause newTy (typeOf <$> es1) <$> eqs)
            pure (patExpr (NodeInfo newTy []) es1 es2)

        EOp1 _ op expr1 -> do
            a <- expr1
            (top, ps) <- inferOp1Type op
            unifyTyped (typeOf a `tArr` newTy) (typeOf top)
            pure (op1Expr (NodeInfo newTy ps) top a)

        EOp2 _ op expr1 expr2 -> do
            a <- expr1
            b <- expr2
            (top, ps) <- inferOp2Type op
            unifyTyped (typeOf a `tArr` typeOf b `tArr` newTy) (typeOf top)
            pure (op2Expr (NodeInfo newTy ps) top a b)

--        EDot _ name expr1 -> do          
--            e1 <- expr1
--            (ty, ps) <- lookupScheme name >>= instantiate
--            unifyTyped (typeOf e1 `tArr` newTy) ty
--            pure (dotExpr (NodeInfo newTy ps) name e1)

        EDot _ expr1 expr2 -> do          
            e1 <- expr1 
            e2 <- expr2 
            unifyTyped e2 (tArr (typeOf e1) newTy)
            pure (dotExpr (NodeInfo newTy []) e1 e2)

            --d<- expr1
            --e1 <- expr1
            --(ty, ps) <- lookupScheme name >>= instantiate
            --unifyTyped (typeOf e1 `tArr` newTy) ty
            --pure (dotExpr (NodeInfo newTy ps) name e1)

        ERec _ fields -> do
            let (_, ns, fs) = unzip3 (fieldList fields)
                info Field{..} = Field{ fieldTag = NodeInfo (typeOf fieldValue) [], .. }
            es <- sequence fs
            unifyTyped newTy (tRecord (zip ns (typeOf <$> es)))
            pure (recExpr (NodeInfo newTy []) (FieldSet (zipWith (info <$$> Field ()) ns es))) 

        ETup _ elems -> do
            tes <- sequence elems
            unifyTyped newTy (tTuple (typeOf <$> tes))
            pure (tupExpr (NodeInfo newTy []) tes)

        ELst _ elems -> do
            tes <- sequence elems
            t1 <- case tes of
                []    -> newTVar kTyp
                (e:_) -> pure (typeOf e)
            unifyTyped newTy (tList t1)
            pure (lstExpr (NodeInfo newTy []) tes)

        -- EAnn Scheme a           

inferPrim :: (Monad m) => Prim -> m Type
inferPrim = pure . \case
    TVoid      -> tVoid
    TUnit      -> tUnit
    TBool{}    -> tBool
    TInt{}     -> tInt
    TInteger{} -> tInteger
--    TNat{}     -> tNat
    TFloat{}   -> tFloat
    TDouble{}  -> tDouble
    TChar{}    -> tChar
    TString{}  -> tString

inferClause
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => Type
  -> [Type]
  -> Clause (Pattern t f g) (m (Ast NodeInfo n o f g c d))
  -> m (Clause (Pattern NodeInfo f g) (Ast NodeInfo n o f g c d))
inferClause ty types clause@(Clause ps _ _) = do
    (tps, vs) <- runWriterT (traverse inferPattern ps)
    let Clause _ exs e = local (second (Env.inserts (toScheme <$$> vs))) <$> clause
    forM_ exs (>>= unifyTyped (tBool :: Type) . typeOf)
    forM_ (zip tps types) (uncurry unifyTyped) 
    e >>= unifyTyped ty . typeOf
    Clause tps <$> sequence exs <*> e

inferPattern
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => Pattern t f g 
  -> WriterT [(Name, Type)] m (Pattern NodeInfo f g)
inferPattern = cata $ \pat -> do
    newTy <- newTVar kTyp
    case pat of
        PVar _ var -> do
            tell [(var, newTy)]
            pure (varPat (NodeInfo newTy []) var)

        PCon _ con ps -> do
            (ty, qs) <- lookupScheme con >>= instantiate
            trs <- sequence ps
            unifyTyped ty (foldr tArr newTy (typeOf <$> trs))
            pure (conPat (NodeInfo newTy qs) con trs)

        PLit _ lit -> do
            ty <- inferPrim lit
            pure (litPat (NodeInfo ty []) lit)

        PRec _ fieldSet -> do
            let (_, ns, fs) = unzip3 (fieldList fieldSet)
            ps <- sequence fs
            let tfs = zipWith (\n p -> Field (patternTag p) n p) ns ps
            unifyTyped newTy (tRecord (zip ns (typeOf <$> ps)))
            pure (recPat (NodeInfo newTy []) (FieldSet tfs))

        PTup _ elems -> do
            ps <- sequence elems
            unifyTyped newTy (tTuple (typeOf <$> ps))
            pure (tupPat (NodeInfo newTy []) ps)

        PLst _ elems -> do
            ps <- sequence elems
            t1 <- case ps of
                []    -> newTVar kTyp
                (p:_) -> pure (typeOf p)
            unifyTyped newTy (tList t1)
            pure (lstPat (NodeInfo newTy []) ps)

        PAs  _ name pat -> do
            tell [(name, newTy)]
            asPat (NodeInfo newTy []) name <$> pat

        POr  _ pat1 pat2 -> do
            p1 <- pat1
            p2 <- pat2
            unifyTyped newTy p1
            unifyTyped newTy p2
            pure (orPat (NodeInfo newTy []) p1 p2)

        PAny _ ->
            pure (anyPat (NodeInfo newTy []))

opType
  :: ( MonadSupply Name m
     -- , MonadReader (ClassEnv (Ast NodeInfo n o f), TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => (NodeInfo -> a)
  -> Scheme
  -> m (a, [Predicate])
opType op scheme = do
    (t, ps) <- instantiate scheme
    pure (op (NodeInfo t ps), ps)

inferOp1Type 
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv (Ast NodeInfo n o f), TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => Op1 t
  -> m (Op1 NodeInfo, [Predicate])
inferOp1Type = \case
    ONeg _ -> opType ONeg (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0))
    ONot _ -> opType ONot (Forall [] [] (tBool `tArr` tBool))

inferOp2Type 
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv (Ast NodeInfo n o f), TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => Op2 t
  -> m (Op2 NodeInfo, [Predicate])
inferOp2Type = \case
    OEq  _ -> opType OEq  (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    ONEq _ -> opType ONEq (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OAdd _ -> opType OAdd (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OMul _ -> opType OMul (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OSub _ -> opType OSub (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OAnd _ -> opType OAnd (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OOr  _ -> opType OOr  (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OLt  _ -> opType OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGt  _ -> opType OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLtE _ -> opType OLtE (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGtE _ -> opType OGtE (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OOpt _ -> opType OOpt (Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0) `tArr` tGen 0 `tArr` tGen 0))
    OScc _ -> opType OScc (Forall [] [] (tString `tArr` tString `tArr` tString))
--    ODiv _ ->
--    OPow _ ->
--    OLArr _ ->
--    ORArr _ ->
--    OFPipe _ ->
--    OBPipe _ ->

instantiate 
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv a, TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => Scheme 
  -> m (Type, [Predicate])
instantiate (Forall kinds ps ty) = do
    names <- supplies (length kinds)
    let ts = zipWith tVar kinds names
        fn p@(InClass cl n) = 
            ( (names !! n, Set.singleton cl)
            , replaceBound ts <$> (tGen <$> p) )
        (pairs, preds) = unzip (fn <$> ps)
    modify (second (`insertAll` pairs))
    pure (replaceBound ts ty, preds)
  where
    insertAll :: Context -> [(Name, Set Name)] -> Context
    insertAll = foldr (uncurry (Env.insertWith Set.union)) 

generalize
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv a, TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => Type
  -> m Scheme
generalize ty = do
    env <- asks snd
    sub <- gets fst
    let ty1 = apply sub ty
        (vs, ks) = unzip $ filter ((`notElem` free (apply sub env)) . fst) (typeVars ty1)
        ixd = Map.fromList (zip vs [0..])
    ps <- lookupPredicates vs
    pure (Forall ks (toPred ixd <$> ps) (apply (tGen <$> Sub ixd) (upgrade ty1)))
  where
    toPred map (var, cl) = InClass cl (fromJust (Map.lookup var map))

lookupPredicates 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m ) 
  => [Name]
  -> m [(Name, Name)]
lookupPredicates vars = do
    env <- gets snd
    pure [(v, cl) | v <- vars, cl <- Set.toList (Env.findWithDefault mempty v env)]

lookupScheme 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, e) m
     , MonadError String m ) 
  => Name 
  -> m Scheme
lookupScheme name = do
    env <- asks snd 
    case Env.lookup name env of
        Nothing     -> throwError ("Unbound type identifier: " <> Text.unpack name)
        Just scheme -> gets (apply . fst) <*> pure scheme

unified 
  :: ( MonadState (Substitution, c) m 
     , MonadError String m ) 
  => Type 
  -> Type 
  -> m Substitution
unified t1 t2 = do
    sub1 <- gets fst
    sub2 <- unify (apply sub1 t1) (apply sub1 t2)
    pure (sub2 <> sub1)

unifyTyped 
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m
     , MonadReader (ClassEnv () () c d, TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m
     , Typed t
     , Typed u ) 
  => t
  -> u
  -> m ()
unifyTyped v1 v2 = do 
    sub <- unified (typeOf v1) (typeOf v2)
    modify (first (sub <>))
    forM_ (Map.toList (getSub sub)) (uncurry propagate)  
  where
    propagate tv ty = do
        env <- gets snd
        propagateClasses ty (fromMaybe mempty (Env.lookup tv env))

propagateClasses 
  :: ( MonadSupply Name m
     --, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m
     , MonadReader (ClassEnv () () () (), TypeEnv) m
     , MonadState (Substitution, Context) m
     , MonadError String m )
  => Type 
  -> Set Name
  -> m ()
propagateClasses (Fix (TVar _ var)) ps 
    | Set.null ps = pure ()
    | otherwise   = modify (second (Env.insertWith Set.union var ps))
propagateClasses ty ps =
    forM_ ps $ \name -> do
        env <- asks fst
        (_ , (preds, _, _)) <- liftEither (lookupClassInstance name ty env)
        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]

--        (_ , Instance preds ty dict) <- liftEither (lookupClassInstance name ty env)
--        -- TODO: super-classes?
--        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]


--propagateClasses (Fix (TVar _ var)) ps 
--    | Set.null ps = pure ()
--    | otherwise   = modify (second (Env.insertWith Set.union var ps))
--propagateClasses ty ps =
--    forM_ ps $ \name -> do
--        env <- asks fst
--        --(_ , Instance preds ty dict) <- liftEither (lookupClassInstance name ty env)
--        --sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]
--        undefined
----        (_ , Instance preds ty dict) <- liftEither (lookupClassInstance name ty env)
----        -- TODO: super-classes?
----        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]

lookupClassInstance 
  -- :: (MapT NodeInfo NodeInfo n n, MapT NodeInfo NodeInfo o o, MonadPlus m, MonadError String m) 
  :: (MonadPlus m, MonadError String m) 
  => Name 
  -> Type 
  -> ClassEnv () () () () -- (Ast NodeInfo n o f) 
--  -> m ([Name], Instance (Ast NodeInfo n o f))
  -> m ([Name], ClassInfo Type (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) () () () ()))
lookupClassInstance name ty env = do
    ((sups, _, _), insts) <- liftMaybe ("No class " <> Text.unpack name) (Env.lookup name env)
    inst <- catchError (msum [tryMatch i | i <- insts]) (const (throwError "Missing class instance"))
    pure (predicateName <$> sups, inst)

--    (sups, _, _, insts) <- liftMaybe ("No class " <> Text.unpack name) (Env.lookup name env)
--    inst <- catchError (msum [tryMatch i | i <- insts]) (const (throwError "Missing class instance"))
--    pure (sups, inst)
  where
    --applyToInstance :: a -> Substitution -> m c
    applyToInstance (ps, ty, x) sub = (apply sub ps, apply sub ty, x)

    tryMatch inst@(_, p, _) = applyToInstance inst <$> match (predicateType p) ty

--    applyToInstance Instance{..} sub = 
--          Instance { predicates   = apply sub predicates
--                   , instanceType = apply sub instanceType
--                   , instanceDict = apply sub instanceDict }
--    tryMatch inst = 
--        applyToInstance inst <$> match (instanceType inst) ty
