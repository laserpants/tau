{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Typecheck where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Except
import Control.Monad.Writer
import Data.Either (lefts)
import Data.Either.Extra (mapLeft)
import Data.Foldable
import Data.Function ((&))
import Data.List (nub)
import Data.Maybe (fromMaybe, fromJust, isNothing)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (first, second, fst3, snd3, thd3, first3, second3, third3)
import Tau.Compiler.Error
import Tau.Compiler.Substitution
import Tau.Compiler.Unification
import Tau.Env (Env(..))
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

inferAst
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Ast t
  -> m (Ast (TypeInfo [Error]))
inferAst (Ast expr) = Ast <$> inferExpr expr

inferExpr
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => ProgExpr t
  -> m (ProgExpr (TypeInfo [Error]))
inferExpr = cata $ \case

    EVar _ var -> inferExprNode varExpr $ do
        ty <- lookupScheme var >>= instantiate
        unifyThis ty
        pure var

    ECon _ con exprs -> inferExprNode (args2 conExpr) $ do
        ty <- lookupScheme con >>= instantiate
        es <- traverse exprNode exprs
        t1 <- thisType
        unify2W ty (foldr tArr t1 (typeOf <$> es))
        pure (con, es)

    ELit _ prim -> inferExprNode litExpr $ do
        ty <- instantiate (primType prim)
        unifyThis ty
        pure prim

    EApp _ exprs -> inferExprNode appExpr $ do
        es <- traverse exprNode exprs
        case es of
            []     -> pure ()
            f:args -> do
                t1 <- thisType
                unify2W f (foldr tArr t1 (typeOf <$> args))
        pure es

    ELet _ (BLet _ pat) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
        (p, vs) <- second nodeVars <$> listen (patternNode (inferPattern pat))

        e1 <- exprNode expr1
        -- Unify bound variable with expression
        unify2W p e1

        schemes <- traverse (secondM generalize) vs
        e2 <- exprNode (local (second3 (Env.inserts schemes)) expr2)
        unifyThis (typeOf e2)

        pure (BLet (TypeInfo (typeOf e1) (exprPredicates e1) []) p, e1, e2)

    ELet _ (BFun _ f pats) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
        (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPattern) pats)

        e1 <- exprNode (local (second3 (Env.inserts (toScheme <$$> vs))) expr1)
        t1 <- newTVar kTyp
        (_, node) <- listen (unify2W t1 (foldr tArr (typeOf e1) (typeOf <$> ps)))
        scheme <- generalize t1

        e2 <- exprNode (local (second3 (Env.insert f scheme)) expr2)
        unifyThis (typeOf e2)

        pure (BFun (TypeInfo t1 (predicates node) []) f ps, e1, e2)

    EFix _ name expr1 expr2 -> inferExprNode (args3 fixExpr) $ do
        t1 <- newTVar kTyp
        e1 <- exprNode (local (second3 (Env.insert name (toScheme t1))) expr1)
        unify2W (t1 :: Type) e1
        scheme <- generalize (typeOf e1)
        e2 <- exprNode (local (second3 (Env.insert name scheme)) expr2)
        unifyThis (typeOf e2)
        pure (name, e1, e2)

    ELam _ pats expr -> inferExprNode (args2 lamExpr) $ do
        (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPattern) pats)
        e1 <- exprNode (local (second3 (Env.inserts (toScheme <$$> vs))) expr)
        unifyThis (foldr tArr (typeOf e1) (typeOf <$> ps))
        pure (ps, e1)

    EIf _ expr1 expr2 expr3 -> inferExprNode (args3 ifExpr) $ do
        e1 <- exprNode expr1
        e2 <- exprNode expr2
        e3 <- exprNode expr3
        unify2W e1 (tBool :: Type)
        unify2W e2 e3
        unifyThis (typeOf e2)
        pure (e1, e2, e3)

    EPat _ exprs eqs -> inferExprNode (args2 patExpr) $ do
        es1 <- traverse exprNode exprs
        es2 <- lift (traverse (inferClause (typeOf <$> es1)) eqs)
        pure (es1, es2)

    EFun _ eqs@(Clause _ ps _:_) -> inferExprNode funExpr $ do
        ty <- newTVar kTyp
        ts <- newTVars kTyp (length ps)
        es <- lift (traverse (inferClause ts) eqs)
        -- Unify return type with r.h.s. of arrow in clauses
        forM_ (clauseGuards =<< es) (\(Guard _ e) -> unify2W (ty :: Type) e)
        -- Also unify return type with the type of clause itself
        forM_ es (unify2W (ty :: Type) . clauseTag)
        -- Check pattern types
        forM_ (clausePatterns <$> es)
            (\ps -> forM_ (zip ps ts) (uncurry unify2W))

        insertPredicates (clausePredicates =<< es)
        unifyThis (foldr tArr ty ts)
        pure es

    EOp1 _ op1 expr -> inferExprNode (args2 op1Expr) $ do
        a <- exprNode expr
        op <- inferOp1 op1
        t1 <- thisType
        unify2W (typeOf a `tArr` t1) (typeOf op)
        pure (op, a)

    EOp2 _ op2 expr1 expr2 -> inferExprNode (args3 op2Expr) $ do
        a <- exprNode expr1
        b <- exprNode expr2
        op <- inferOp2 op2
        t1 <- thisType
        unify2W (typeOf a `tArr` typeOf b `tArr` t1) (typeOf op)
        pure (op, a, b)

    ETuple _ exprs -> inferExprNode tupleExpr $ do
        es <- traverse exprNode exprs
        unifyThis (tTuple (typeOf <$> es))
        pure es

    EList _ exprs -> inferExprNode listExpr $ do
        es <- traverse exprNode exprs
        t1 <- case es of
            []    -> newTVar kTyp
            (e:_) -> pure (typeOf e)

        -- Unify list elements' types
        (_, node) <- listen (forM_ es (unify2W t1))
        when (nodeHasErrors node) $
            insertErrors [ListElemUnficationError]

        unifyThis (tList t1)
        pure es

    ERecord _ row -> inferExprNode recordExpr $ do
        fs <- traverse exprNode row
        unifyThis (tRecord (rowToType (typeOf <$> fs)))
        pure fs

inferPattern
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => ProgPattern t
  -> m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
inferPattern = cata $ \case

    PVar _ var -> inferPatternNode varPat $ do
        t <- thisType
        tellVars [(var, t)]
        pure var

    PCon _ con pats -> inferPatternNode (args2 conPat) $ do
        lookupConstructor con >>= \case
            Nothing -> pure ()
            Just (_, arity) -> do
                -- The number of arguments must match arity of constructor
                when (arity /= length pats) $
                    insertErrors [ConstructorPatternArityMismatch con arity (length pats)]

        ty <- lookupScheme con >>= instantiate
        ps <- traverse patternNode pats

        t1 <- thisType
        (_, node) <- listen (unify2W ty (foldr tArr t1 (typeOf <$> ps)))
        when (nodeHasErrors node) $
            insertErrors [ConstructorPatternTypeMismatch con]

        pure (con, ps)

    PLit _ prim -> inferPatternNode litPat $ do
        t <- instantiate (primType prim)
        unifyThis t
        pure prim

    PAs _ var pat -> inferPatternNode (args2 asPat) $ do
        p <- patternNode pat
        t <- thisType
        tellVars [(var, t)]
        unifyThis (typeOf p)
        pure (var, p)

    POr _ pat1 pat2 -> inferPatternNode (args2 orPat) $ do
        p1 <- patternNode pat1
        p2 <- patternNode pat2
        unifyThis (typeOf p1)
        unifyThis (typeOf p2)
        pure (p1, p2)

    PAny _ ->
        inferPatternNode (args0 anyPat) $ pure ()

    PTuple t pats -> inferPatternNode tuplePat $ do
        ps <- traverse patternNode pats
        unifyThis (tTuple (typeOf <$> ps))
        pure ps

    PList t pats -> inferPatternNode listPat $ do
        ps <- traverse patternNode pats
        t1 <- case ps of
            []    -> newTVar kTyp
            (p:_) -> pure (typeOf p)

        -- Unify list elements' types
        (_, node) <- listen (forM_ ps (unify2W t1))
        when (nodeHasErrors node) $
            insertErrors [ListPatternElemUnficationError]

        unifyThis (tList t1)
        pure ps

    PRecord t row -> inferPatternNode recordPat $ do
        fs <- traverse patternNode row
        unifyThis (tRecord (rowToType (typeOf <$> fs)))
        pure fs

patternNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
  -> WriterT Node m (ProgPattern (TypeInfo [Error]))
patternNode pat = do
    (p, vs) <- lift pat
    insertPredicates (patternPredicates p)
    tellVars vs
    pure p

exprNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m (ProgExpr (TypeInfo [Error]))
exprNode expr = do
    e <- lift expr
    insertPredicates (exprPredicates e)
    pure e

thisType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => WriterT Node m Type
thisType = do
    t <- newTVar kTyp
    unifyThis t
    pure t

opType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => (TypeInfo [Error] -> a)
  -> Scheme
  -> WriterT Node m a
opType op scheme = do
    (t, (_, _, ps, es)) <- listen (instantiate scheme)
    pure (op (TypeInfo t ps es))

inferOp1
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Op1 t
  -> WriterT Node m (Op1 (TypeInfo [Error]))
inferOp1 = \case
    ONeg _ -> opType ONeg (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0))
    ONot _ -> opType ONot (Forall [] [] (tBool `tArr` tBool))

inferOp2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Op2 t
  -> WriterT Node m (Op2 (TypeInfo [Error]))
inferOp2 = \case
    OEq  _ -> opType OEq  (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    ONeq _ -> opType ONeq (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OAdd _ -> opType OAdd (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OMul _ -> opType OMul (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OSub _ -> opType OSub (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OAnd _ -> opType OAnd (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OOr  _ -> opType OOr  (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OLt  _ -> opType OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGt  _ -> opType OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLte _ -> opType OLte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGte _ -> opType OGte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))

inferClause
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => [Type]
  -> Clause t (ProgPattern t) (m (ProgExpr (TypeInfo [Error])))
  -> m (ProgClause (TypeInfo [Error]))
inferClause tys eq@(Clause _ pats _) = inferExprNode (args2 Clause) $ do
    (ps, (_, vs, _, _)) <- listen (traverse (patternNode . inferPattern) pats)
    let schemes = toScheme <$$> vs
        Clause _ _ guards = local (second3 (Env.inserts schemes)) <$> eq
        (iffs, es) = unzip (guardPair <$> guards)
    -- Conditions must be Bool
    forM_ (concat iffs) unifyIffCondition
    gs <- traverse inferGuard guards
    pure (ps, gs)

inferGuard
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Guard (m (ProgExpr (TypeInfo [Error])))
  -> WriterT Node m (Guard (ProgExpr (TypeInfo [Error])))
inferGuard (Guard exprs expr) = Guard <$> traverse exprNode exprs <*> exprNode expr

unifyIffCondition
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m ()
unifyIffCondition expr = do
    e <- lift expr
    (_, node) <- listen (unify2W (tBool :: Type) e)
    when (nodeHasErrors node) $
        insertErrors [NonBooleanGuardCondition]

primType :: Prim -> Scheme
primType = \case

    TUnit      -> Forall [] [] tUnit
    TBool{}    -> Forall [] [] tBool
    TChar{}    -> Forall [] [] tChar
    TString{}  -> Forall [] [] tString
    TInt{}     -> Forall [kTyp] [InClass "Num" 0] (tGen 0)
    TInteger{} -> Forall [kTyp] [InClass "Num" 0] (tGen 0)
    TFloat{}   -> Forall [kTyp] [InClass "Fractional" 0] (tGen 0)
    TDouble{}  -> Forall [kTyp] [InClass "Fractional" 0] (tGen 0)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

newTVar :: (MonadSupply Name m) => Kind -> m (TypeT a)
newTVar kind = tVar kind <$> supply

newTVars :: (MonadSupply Name m) => Kind -> Int -> m [TypeT a]
newTVars kind n = tVar kind <$$> supplies n

instantiate
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Scheme
  -> WriterT Node m Type
instantiate (Forall kinds preds ty) = do
    names <- supplies (length kinds)
    let ts = zipWith tVar kinds names
        (pairs, ps) = unzip (fn <$> preds)
        fn p@(InClass tc ix) =
            ( (names !! ix, Set.singleton tc)
            , replaceBound ts <$> (tGen <$> p) )
    modify (second (`insertAll` pairs))
    insertPredicates ps
    pure (replaceBound ts ty)

generalize
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Type
  -> m Scheme
generalize ty = do
    env <- asks snd3
    sub <- gets fst
    let typ = apply sub ty
        frees = free (apply sub env)
        (vs, ks) = unzip $ filter ((`notElem` frees) . fst) (typeVars typ)
        inxd = Map.fromList (zip vs [0..])
    ps <- lookupPredicates vs
    pure (Forall ks (toPred inxd <$> ps) (apply (Sub (tGen <$> inxd)) (upgrade typ)))
  where
    toPred map (var, tc) = InClass tc (fromJust (Map.lookup var map))

insertAll :: Context -> [(Name, Set Name)] -> Context
insertAll = foldr (uncurry (Env.insertWith Set.union))

lookupConstructor
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Name
  -> WriterT Node m (Maybe (Set Name, Int))
lookupConstructor con = do
    env <- asks thd3
    let info = Env.lookup con env
    when (isNothing info) (insertErrors [NoDataConstructor con])
    pure info

lookupScheme
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Name
  -> WriterT Node m Scheme
lookupScheme name = do
    env <- asks snd3
    sub <- gets fst
    case Env.lookup name env of
        Nothing -> do
            insertErrors [UnboundTypeIdentifier name]
            toScheme <$> newTVar kTyp
        Just ty ->
            pure (apply sub ty)

lookupPredicates
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => [Name]
  -> m [(Name, Name)]
lookupPredicates vars = do
    env <- gets snd
    pure [(v, tc) | v <- vars, tc <- Set.toList (Env.findWithDefault mempty v env)]

unified
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m )
  => Type
  -> Type
  -> m TypeSubstitution
unified t1 t2 = do
    sub1 <- gets fst
    case runExcept (unify (apply sub1 t1) (apply sub1 t2)) of
        Left err  -> throwError (CannotUnify t1 t2 err)
        Right sub -> pure sub

unify2
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m
     , Typed u
     , Typed v )
  => u
  -> v
  -> m ()
unify2 a b = do
    sub <- unified (typeOf a) (typeOf b)
    modify (first (sub <>))
    forM_ (Map.toList (getSub sub)) (uncurry propagate)
  where
    propagate tv ty = do
        env <- gets snd
        propagateClasses ty (fromMaybe mempty (Env.lookup tv env))

unify2W
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , Typed u
     , Typed v
     , Substitutable u Void
     , Substitutable v Void )
  => u
  -> v
  -> WriterT Node m ()
unify2W a b = do
    sub <- gets fst
    runUnify (apply sub a) (apply sub b) >>= whenLeft (insertErrors . pure)

propagateClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m )
  => Type
  -> Set Name
  -> m ()
propagateClasses (Fix (TVar _ var)) ps
    | Set.null ps = pure ()
    | otherwise   = modify (second (Env.insertWith Set.union var ps))
propagateClasses ty ps =
    forM_ ps $ \name -> do
        env <- asks fst3
        ClassInfo{ classSuper = preds } <- lookupClassInstance name ty env
        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]

lookupClassInstance
  :: ( MonadState (TypeSubstitution, Context) m
     , MonadError Error m )
  => Name
  -> Type
  -> ClassEnv
  -> m (ClassInfo Type (Ast (TypeInfo ())))
lookupClassInstance tc ty env = do
    (ClassInfo{..}, insts) <- liftMaybe (MissingClass tc) (Env.lookup tc env)
    msum [tryMatch i | i <- insts] &
        maybe (throwError (MissingInstance tc ty)) pure
  where
    tryMatch info@ClassInfo{..} =
        case match (predicateType classSignature) ty of
            Left{}    -> Nothing
            Right sub -> Just (apply sub info)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

args0 :: (TypeInfo [Error] -> a) -> TypeInfo [Error] -> () -> a
args0 f ti () = f ti

args2 :: (TypeInfo [Error] -> t1 -> t2 -> a) -> TypeInfo [Error] -> (t1, t2) -> a
args2 f ti (a, b) = f ti a b

args3 :: (TypeInfo [Error] -> t1 -> t2 -> t3 -> a) -> TypeInfo [Error] -> (t1, t2, t3) -> a
args3 f ti (a, b, c) = f ti a b c

inferPatternNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => (TypeInfo [Error] -> t -> a)
  -> WriterT Node m t
  -> m (a, [(Name, Type)])
inferPatternNode c f = do
    newTy <- newTVar kTyp
    (a, ti, vs) <- inferNode newTy f
    pure (c ti a, vs)

inferExprNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => (TypeInfo [Error] -> t1 -> a)
  -> WriterT Node m t1
  -> m a
inferExprNode c f = do
    newTy <- newTVar kTyp
    (a, ti, _) <- inferNode newTy f
    pure (c ti a)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Type class instances

instance (Typed t) => Typed (ProgExpr t) where
    typeOf = typeOf . exprTag

instance (Typed t) => Typed (ProgPattern t) where
    typeOf = typeOf . patternTag

instance (Typed t) => Typed (Op1 t) where
    typeOf = typeOf . op1Tag

instance (Typed t) => Typed (Op2 t) where
    typeOf = typeOf . op2Tag

instance (Typed t) => Typed (Ast t) where
    typeOf = typeOf . astTag

instance Substitutable (ClassInfo Type (Ast (TypeInfo e))) Void where
    apply sub ClassInfo{..} =
        ClassInfo{ classSuper     = apply sub classSuper
                 , classSignature = apply sub classSignature
                 , .. }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Node = ([Type], [(Name, Type)], [Predicate], [Error])

unifyThis :: (MonadWriter Node m) => Type -> m ()
unifyThis ty = tell ([ty], mempty, mempty, mempty)

tellVars :: (MonadWriter Node m) => [(Name, Type)] -> m ()
tellVars vs = tell (mempty, vs, mempty, mempty)

insertPredicates :: (MonadWriter Node m) => [Predicate] -> m ()
insertPredicates ps = tell (mempty, mempty, ps, mempty)

insertErrors :: (MonadWriter Node m) => [Error] -> m ()
insertErrors es = tell (mempty, mempty, mempty, es)

nodeHasErrors :: Node -> Bool
nodeHasErrors (_, _, _, es) = not (Prelude.null es)

predicates :: Node -> [Predicate]
predicates (_, _, ps, _) = ps

errors :: Node -> [Error]
errors (_, _, _, es) = es

nodeVars :: Node -> [(Name, Type)]
nodeVars (_, vs, _, _) = vs

inferNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Type
  -> WriterT Node m a
  -> m (a, TypeInfo [Error], [(Name, Type)])
inferNode t w = do
    (a, (ts, vs, ps, err)) <- runWriterT w
    errs <- lefts <$> mapM (runUnify t) ts
    sub <- gets fst
    pure (a, TypeInfo t (nub (apply sub ps)) (err <> errs), vs)

runUnify
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , Typed u
     , Typed v )
  => u
  -> v
  -> m (Either Error ())
runUnify = runExceptT <$$> unify2

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Monad transformer stack

type InferState   = StateT (TypeSubstitution, Context)
type InferReader  = ReaderT (ClassEnv, TypeEnv, ConstructorEnv)
type InferSupply  = SupplyT Name
type InferStack a = InferReader (InferState (InferSupply a))

runInferState :: (Monad m) => Context -> InferState m a -> m (a, (TypeSubstitution, Context))
runInferState context = flip runStateT (mempty, context)

runInferReader :: (Monad m) => ClassEnv -> TypeEnv -> ConstructorEnv -> InferReader m r -> m r
runInferReader e1 e2 e3 = flip runReaderT (e1, e2, e3)

runInferSupply :: (Monad m) => InferSupply m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

runInfer
  :: (Monad m)
  => Context
  -> ClassEnv
  -> TypeEnv
  -> ConstructorEnv
  -> InferStack m a
  -> m (a, TypeSubstitution, Context)
runInfer context classEnv typeEnv constructorEnv =
    runInferReader classEnv typeEnv constructorEnv
    >>> runInferState context
    >>> runInferSupply
    >>> fmap to
