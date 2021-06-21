{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Typecheck where

import Control.Monad.Except 
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Either (fromLeft, lefts)
import Data.Either.Extra (mapLeft)
import Data.Maybe (fromMaybe, fromJust, isNothing)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (first, second, fst3, snd3, thd3, first3, second3, third3)
import Tau.Compiler.Error
import Tau.Compiler.Substitute
import Tau.Compiler.Unify
import Tau.Lang
import Tau.Prog
import Tau.Tooling
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

inferAstType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Ast t
  -> m (Ast (TypeInfo [Error]))
inferAstType (Ast expr) = do
    e <- inferExprType expr
    sub <- subs
    pure (simplifyPredicates <$> Ast (packRows (applyBoth sub e)))

packRows 
  :: ProgExpr (TypeInfo [Error])
  -> ProgExpr (TypeInfo [Error])
packRows = cata $ \case

    EVar t var -> 
        if isRecordType (nodeType t)
            then conExpr (TypeInfo [] (nodeType t) []) "#" [varExpr (fromJust . unpackRecordType <$> t) var]
            else varExpr t var

    e -> embed e

inferExprType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgExpr t
  -> m (ProgExpr (TypeInfo [Error]))
inferExprType = cata $ \case

    EVar _ var -> do 
        (a, ti, _) <- runNode $ do
            ty <- lookupScheme var >>= instantiate
            unfiyWithNode ty
            pure var
        pure (varExpr ti a)

    ECon _ con exprs -> do
        (es, ti, _) <- runNode $ do
            ty <- lookupScheme con >>= instantiate
            es <- traverse exprNode exprs
            t1 <- thisNodeType
            ty ## foldr tArr t1 (typeOf <$> es)
            pure es
        pure (conExpr ti con es)

    ELit _ prim -> do
        (_, ti, _) <- runNode $ do
            ty <- instantiate (primType prim)
            unfiyWithNode ty
        pure (litExpr ti prim)

    EApp _ exprs -> do
        (es, ti, _) <- runNode $ do
            es <- traverse exprNode exprs
            case es of
                [] -> pure ()
                f:args -> do
                    t1 <- thisNodeType
                    f ## foldr tArr t1 (typeOf <$> args)
            pure es
        pure (appExpr ti es)

    EFix _ name expr1 expr2 -> do
        ((e1, e2), ti, _) <- runNode $ do
            t1 <- newTVar 
            e1 <- exprNode (local (inTypeEnv (Env.insert name (toScheme t1))) expr1)
            e1 ## (t1 :: Type) 
            scheme <- generalize (typeOf e1)
            e2 <- exprNode (local (inTypeEnv (Env.insert name scheme)) expr2)
            unfiyWithNode (typeOf e2)
            pure (e1, e2)
        pure (fixExpr ti name e1 e2)

    ELam _ pats expr -> do
        ((ps, e1), ti, _) <- runNode $ do
            (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPatternType) pats)
            e1 <- exprNode (local (inTypeEnv (Env.inserts (toScheme <$$> vs))) expr)
            unfiyWithNode (foldr tArr (typeOf e1) (typeOf <$> ps))
            pure (ps, e1)
        pure (lamExpr ti ps e1)

    EIf _ expr1 expr2 expr3 -> do
        ((e1, e2, e3), ti, _) <- runNode $ do
            e1 <- exprNode expr1
            e2 <- exprNode expr2
            e3 <- exprNode expr3
            e1 ## (tBool :: Type)
            e2 ## e3
            unfiyWithNode (typeOf e2)
            pure (e1, e2, e3)
        pure (ifExpr ti e1 e2 e3)

    EPat _ expr eqs -> do
        ((e1, cs), ti, _) <- runNode $ do
            e1 <- exprNode expr
            cs <- lift (traverse (inferClauseType (typeOf e1)) eqs)
            tellPredicates (clausePredicates =<< cs)
            -- Unify pattern clauses
            forM_ cs $ \(Clause t p gs) -> do
                forM_ gs (\(Guard _ e) -> unfiyWithNode (typeOf e))
                unfiyWithNode (typeOf t)
                e1 ## p
            pure (e1, cs)
        pure (patExpr ti e1 cs)

    ELet _ (BPat _ pat) expr1 expr2 -> do
        ((b, e1, e2), ti, _) <- runNode $ do
            (p, vs) <- second nodeVars <$> listen (patternNode (inferPatternType pat))
            e1 <- exprNode expr1
            -- Unify bound variable with expression
            p ## e1
            schemes <- traverse (secondM generalize) vs
            e2 <- exprNode (local (inTypeEnv (Env.inserts schemes)) expr2)
            unfiyWithNode (typeOf e2)
            (_, ti, _) <- runNode $ do
                unfiyWithNode (typeOf e1)
                tellPredicates (exprPredicates e1 <> exprPredicates e2)
                tellPredicates (patternPredicates p)
            pure (BPat ti p, e1, e2)
        pure (letExpr ti b e1 e2)

    ELet _ (BFun _ f pats) expr1 expr2 -> do
        ((b, e1, e2), ti, _) <- runNode $ do
            (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPatternType) pats)
            e1 <- exprNode (local (inTypeEnv (Env.inserts (toScheme <$$> vs))) expr1)
            t1 <- newTVar 
            t1 ## foldr tArr (typeOf e1) (typeOf <$> ps)
            scheme <- generalize t1
            e2 <- exprNode (local (inTypeEnv (Env.insert f scheme)) expr2)
            unfiyWithNode (typeOf e2)
            (_, ti, _) <- runNode $ do
                unfiyWithNode t1
                tellPredicates (exprPredicates e1 <> exprPredicates e2)
                tellPredicates (patternPredicates =<< ps)
            pure (BFun ti f ps, e1, e2)
        pure (letExpr ti b e1 e2)

    EFun _ eqs -> do
        (cs, ti, _) <- runNode $ do
            ty <- newTVar 
            t1 <- thisNodeType
            cs <- lift (traverse (inferClauseType t1) eqs)
            tellPredicates (clausePredicates =<< cs)
            -- Unify pattern clauses
            forM_ cs $ \(Clause t p gs) -> do
                forM_ gs (\(Guard _ e) -> t ## e >> t1 ## (ty `tArr` typeOf e))
                p ## ty
            pure cs
        pure (funExpr ti cs)

    EOp1 _ op1 expr -> do
        ((op, a), ti, _) <- runNode $ do
            a <- exprNode expr
            op <- inferOp1Type op1
            t1 <- thisNodeType
            op ## (typeOf a `tArr` t1)
            pure (op, a)
        pure (op1Expr ti op a)

    EOp2 _ op2 expr1 expr2 -> do
        ((op, a, b), ti, _) <- runNode $ do
--            a <- exprNode expr1
--            b <- exprNode expr2
--            op <- inferOp2Type op2
--            t1 <- thisNodeType
--            op ## (typeOf a `tArr` typeOf b `tArr` t1) 
--            pure (op, a, b)

            a <- exprNode expr1
            b <- exprNode expr2

            let getRowField = case (a, unpackRecordType (typeOf b)) of
                  (Fix (EVar _ name), Just row) -> do
                      t <- lookupRowType name row
                      pure (name, t)
                  _ -> 
                      Nothing

            case (op2, getRowField) of
                (ODot _, Just (name, t)) -> do
                    unfiyWithNode t
                    op <- inferOp2Type (OField ())
                    op ## (typeOf a `tArr` typeOf b `tArr` t) 
                    pure (op, litExpr (TypeInfo [] tAtom []) (TAtom name), b)

                _ -> do
                    op <- inferOp2Type op2
                    t1 <- thisNodeType
                    op ## (typeOf a `tArr` typeOf b `tArr` t1) 
                    pure (op, a, b)

        pure (op2Expr ti op a b)

    ETuple _ exprs -> do
        (es, ti, _) <- runNode $ do
            es <- traverse exprNode exprs
            unfiyWithNode (tTuple (typeOf <$> es))
            pure es
        pure (tupleExpr ti es)

    EList _ exprs -> do
        (es, ti, _) <- runNode $ do
            es <- traverse exprNode exprs
            t1 <- case es of
                []    -> newTVar 
                (e:_) -> pure (typeOf e)
            -- Unify list elements' types
            (_, node) <- listen (forM_ es (## t1))
            when (nodeHasErrors node) $ tellErrors [ListElemUnficationError]
            unfiyWithNode (tList t1)
            pure es
        pure (listExpr ti es)

    ERow _ label expr row -> do
        ((e, r), ti, _) <- runNode $ do
            e <- exprNode expr
            r <- exprNode row
            unfiyWithNode (tRow label (typeOf e) (typeOf r))
            pure (e, r)
        pure (rowExpr ti label e r)

    EAnn t expr -> do
        e <- expr
        _ <- runNode $ e ## t
        pure e

inferPatternType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgPattern t
  -> m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
inferPatternType = cata $ \case

    PVar _ var -> do
        (_, ti, vs) <- runNode $ do
            t <- thisNodeType
            tellVars [(var, t)]
        pure (varPat ti var, vs)

    PCon _ con pats -> do
        (ps, ti, vs) <- runNode $ do
            lookupConstructor con >>= \case
                Nothing -> pure ()
                Just (_, arity) -> do
                    -- The number of arguments must match arity of constructor
                    when (arity /= length pats) $
                        tellErrors [ConstructorPatternArityMismatch con arity (length pats)]
            ty <- lookupScheme con >>= instantiate
            ps <- traverse patternNode pats
            t1 <- thisNodeType
            (_, node) <- listen (ty ## foldr tArr t1 (typeOf <$> ps))
            when (nodeHasErrors node) $
                tellErrors [ConstructorPatternTypeMismatch con]
            pure ps
        pure (conPat ti con ps, vs)

    PAs _ var pat -> do
        (p, ti, vs) <- runNode $ do
            p <- patternNode pat
            t <- thisNodeType
            tellVars [(var, t)]
            unfiyWithNode (typeOf p)
            pure p
        pure (asPat ti var p, vs)

    PLit _ prim -> do
        (_, ti, vs) <- runNode $ do
            t <- instantiate (primType prim)
            unfiyWithNode t
        pure (litPat ti prim, vs)

    PAny _ -> do
        (_, ti, vs) <- runNode $ pure ()
        pure (anyPat ti, vs)

    POr _ pat1 pat2 -> do
        ((p1, p2), ti, vs) <- runNode $ do
            p1 <- patternNode pat1
            p2 <- patternNode pat2
            unfiyWithNode (typeOf p1)
            unfiyWithNode (typeOf p2)
            pure (p1, p2)
        pure (orPat ti p1 p2, vs)

    PTuple t pats -> do
        (ps, ti, vs) <- runNode $ do
            ps <- traverse patternNode pats
            unfiyWithNode (tTuple (typeOf <$> ps))
            pure ps
        pure (tuplePat ti ps, vs)

    PList t pats -> do
        (ps, ti, vs) <- runNode $ do
            ps <- traverse patternNode pats
            t1 <- case ps of
                []    -> newTVar 
                (p:_) -> pure (typeOf p)
            -- Unify list elements' types
            (_, node) <- listen (forM_ ps (## t1))
            when (nodeHasErrors node) $ tellErrors [ListPatternElemUnficationError]
            unfiyWithNode (tList t1)
            pure ps
        pure (listPat ti ps, vs)

    PRow _ label pat row -> do
        ((p, r), ti, vs) <- runNode $ do
            p <- patternNode pat
            (r, vs) <- lift row
            tellPredicates (patternPredicates r)

            case project r of
                PVar{} -> tellVars (second (tRecord) <$> vs)
                _      -> tellVars vs

            unfiyWithNode (tRow label (typeOf p) (typeOf r))
            pure (p, r)

--            case project r of
--                PVar{} -> do
--                    unfiyWithNode (tRow label (typeOf p) (typeOf r))
--                    pure (p, r)
--                    --let q = tRecord (typeOf r)
--                    --unfiyWithNode (tRow label (typeOf p) q)
--                    --pure (p, conPat (TypeInfo [] q []) "#" [r])
--                _ -> do
--                    unfiyWithNode (tRow label (typeOf p) (typeOf r))
--                    pure (p, r)

        pure (rowPat ti label p r, vs)

    PAnn t pat -> do
        p <- pat
        _ <- runNode $ fst p ## t
        pure p

opType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => (TypeInfo [Error] -> a)
  -> Scheme
  -> WriterT Node m a
opType op scheme = do
    (t, (_, _, ps, es)) <- listen (instantiate scheme)
    pure (op (TypeInfo es t ps))

inferOp1Type
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Op1 t
  -> WriterT Node m (Op1 (TypeInfo [Error]))
inferOp1Type = \case
    ONeg _ -> opType ONeg (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0))
    ONot _ -> opType ONot (Forall [] [] (tBool `tArr` tBool))

inferOp2Type
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Op2 t
  -> WriterT Node m (Op2 (TypeInfo [Error]))
inferOp2Type = \case
    OEq    _ -> opType OEq  (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    ONeq   _ -> opType ONeq (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OAdd   _ -> opType OAdd (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OMul   _ -> opType OMul (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OSub   _ -> opType OSub (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OAnd   _ -> opType OAnd (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OOr    _ -> opType OOr  (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OLt    _ -> opType OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGt    _ -> opType OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLte   _ -> opType OLte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGte   _ -> opType OGte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    ODot   _ -> opType ODot (Forall [kTyp, kTyp] [] ((tGen 0 `tArr` tGen 1) `tArr` tGen 0 `tArr` tGen 1))
    OField _ -> opType OField (Forall [kTyp, kTyp] [] (tCon kTyp "Atom" `tArr` tGen 1 `tArr` tGen 0))

inferClauseType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> Clause t (ProgPattern t) (m (ProgExpr (TypeInfo [Error])))
  -> m (ProgClause (TypeInfo [Error]))
inferClauseType ty eq@(Clause _ pat _) = do
    ((p, gs), ti, _) <- runNode $ do
        (p, (_, vs, _, _)) <- listen (patternNode (inferPatternType pat)) 
        let schemes = toScheme <$$> vs
            Clause _ _ guards = local (inTypeEnv (Env.inserts schemes)) <$> eq
            (iffs, _) = unzip (guardToPair <$> guards)
        -- Iff-conditions must be Bool
        forM_ (concat iffs) unifyIffCondition
        gs <- traverse inferGuard guards
        pure (p, gs)
    pure (Clause ti p gs)

unifyIffCondition
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m ()
unifyIffCondition expr = do
    e <- lift expr
    (_, node) <- listen (e ## (tBool :: Type))
    when (nodeHasErrors node) $ tellErrors [GuardConditionNotABool]

inferGuard
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Guard (m (ProgExpr (TypeInfo [Error])))
  -> WriterT Node m (Guard (ProgExpr (TypeInfo [Error])))
inferGuard (Guard es e) = Guard <$> traverse exprNode es <*> exprNode e

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
    TAtom{}    -> Forall [kTyp] [] (tGen 0)

exprNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m (ProgExpr (TypeInfo [Error]))
exprNode expr = do
    e <- lift expr
    tellPredicates (exprPredicates e)
    pure e

patternNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
  -> WriterT Node m (ProgPattern (TypeInfo [Error]))
patternNode pat = do
    (p, vs) <- lift pat
    tellPredicates (patternPredicates p)
    tellVars vs
    pure p

thisNodeType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => WriterT Node m Type
thisNodeType = do
    t <- newTVar 
    unfiyWithNode t
    pure t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

lookupScheme
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> WriterT Node m Scheme
lookupScheme name = do
    env <- asks getTypeEnv
    sub <- lift subs
    case Env.lookup name env of
        Nothing -> do
            tellErrors [NotInScope name]
            toScheme <$> newTVar 

        Just ty ->
            pure (applyBoth sub ty)

lookupPredicates
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => [Name]
  -> m [(Name, Name)]
lookupPredicates vars = do
    env <- gets thd3
    pure $ do
        v  <- vars
        tc <- Set.toList (Env.findWithDefault mempty v env)
        [(v, tc)]

lookupConstructor
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> WriterT Node m (Maybe (Set Name, Int))
lookupConstructor con = do
    env <- asks getConstructorEnv
    let info = Env.lookup con env
    when (isNothing info) (tellErrors [MissingDataConstructor con])
    pure info

instantiate
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Scheme
  -> WriterT Node m Type
instantiate (Forall kinds preds ty) = do
    names <- ("a" <>) <$$> supplies (length kinds)
    let ts = zipWith tVar kinds names
        (pairs, ps) = unzip (fn <$> preds)
        fn p@(InClass tc ix) =
            ( (names !! ix, Set.singleton tc)
            , fromPolytype ts <$> (tGen <$> p) )
    addToContext pairs
    tellPredicates ps
    pure (fromPolytype ts ty)

generalize
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> m Scheme
generalize ty = do
     env <- askTypeEnv
     sub <- subs
     let ty1 = applyBoth sub ty
         frees = fst <$> free (applyBoth sub env)
         (vs, ks) = unzip $ filter ((`notElem` frees) . fst) (typeVars ty1)
         ixd = Map.fromList (zip vs [0..])
     ps <- lookupPredicates vs
     pure (Forall ks (toPred ixd <$> ps) (apply (Sub (tGen <$> ixd)) (toPolytype ty1)))
  where
    toPred map (var, tc) = InClass tc (fromJust (Map.lookup var map))

propagateClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m
     , MonadError Error m )
  => Type
  -> Set Name
  -> m ()
propagateClasses (Fix (TVar _ var)) ps
    | Set.null ps = pure ()
    | otherwise   = modify (third3 (Env.insertWith Set.union var ps))
propagateClasses ty ps =
    forM_ ps $ \name -> do
        env <- asks getClassEnv
        ClassInfo{ classSuper = preds } <- lookupClassInstance name ty env
        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]

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

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Node = 
    ( List Type           -- Types to unify with the node's type
    , List (Name, Type)   -- Pattern variables
    , List Predicate      -- Class predicates
    , List Error          -- Errors
    )

unfiyWithNode :: (MonadWriter Node m) => Type -> m ()
unfiyWithNode ty = tell ([ty], mempty, mempty, mempty)

tellVars :: (MonadWriter Node m) => [(Name, Type)] -> m ()
tellVars vs = tell (mempty, vs, mempty, mempty)

tellPredicates :: (MonadWriter Node m) => [Predicate] -> m ()
tellPredicates ps = tell (mempty, mempty, ps, mempty)

tellErrors :: (MonadWriter Node m) => [Error] -> m ()
tellErrors es = tell (mempty, mempty, mempty, es)

nodeVars :: Node -> [(Name, Type)]
nodeVars (_, vs, _, _) = vs

nodeHasErrors :: Node -> Bool
nodeHasErrors (_, _, _, es) = not (Prelude.null es)

newTVar :: (MonadSupply Name m) => m (TypeT a)
newTVar = do
    k <- ("k" <>) <$> supply
    t <- ("a" <>) <$> supply
    pure (tVar (kVar k) t)

insertAll :: Context -> [(Name, Set Name)] -> Context
insertAll = foldr (uncurry (Env.insertWith Set.union))

addToContext :: (MonadState (a, b, Context) m) => [(Name, Set Name)] -> m ()
addToContext ps = modify (third3 (`insertAll` ps))

runNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => WriterT Node m a
  -> m (a, TypeInfo [Error], [(Name, Type)])
runNode writer = do
    t <- newTVar
    (a, (ts, vs, ps, es)) <- runWriterT writer
    es2 <- concat <$> mapM (doUnify t) ts
    -- TODO
    -- inferKind???
    -- t' <- inferKind (apply sub t)
    sub <- subs
    pure ( a
         , simplifyPredicates (TypeInfo (es <> es2) (applyBoth sub t) (applyBoth sub ps))
         , vs )

doUnify 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> Type 
  -> m [Error]
doUnify t1 t2 = do
    sub <- subs
    either pure (const []) <$> runExceptT (do
        (typeSub, kindSub) <- withExceptT (CannotUnify t1 t2) (unifyTypes (applyBoth sub t1) (applyBoth sub t2))
        modify (first3 (typeSub <>))
        modify (second3 (kindSub <>))
-- TODO
-- --        runUnifyKinds (kindOf t1) (kindOf t2)

        forM_ (Map.toList (getSub typeSub)) (uncurry propagate))
  where
    propagate tv ty = do
        env <- gets thd3
        propagateClasses ty (fromMaybe mempty (Env.lookup tv env))

(##)
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m 
     , Typed a1
     , Typed a2 )
  => a1 
  -> a2
  -> WriterT Node m ()
(##) e1 e2 = doUnify (typeOf e1) (typeOf e2) >>= tellErrors 

subs
  :: (MonadState (Substitution Type, Substitution Kind, a) m)
  => m (Substitution Type, Substitution Kind)
subs = do
    (typeSub, kindSub, _) <- get
    pure (typeSub, kindSub)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--import Control.Arrow ((<<<), (>>>))
--import Control.Monad.Except (MonadError, catchError, throwError)
--import Control.Monad.Reader
--import Control.Monad.State
--import Control.Monad.Supply
--import Control.Monad.Trans.Except
--import Control.Monad.Writer
--import Data.Either (lefts)
--import Data.Either.Extra (mapLeft)
--import Data.Foldable
--import Data.Function ((&))
--import Data.List (nub)
--import Data.Maybe (fromMaybe, fromJust, isNothing)
--import Data.Set.Monad (Set)
--import Data.Tuple.Extra (first, second, fst3, snd3, thd3, first3, second3, third3)
--import Tau.Compiler.Error
--import Tau.Compiler.Substitute
--import Tau.Compiler.Unify
--import Tau.Env (Env(..))
--import Tau.Lang
--import Tau.Pretty
--import Tau.Prog
--import Tau.Tooling
--import Tau.Type
--import qualified Data.Map.Strict as Map
--import qualified Data.Set.Monad as Set
--import qualified Data.Text as Text
--import qualified Tau.Env as Env

-- inferKind 
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Type
--   -> m Type
-- inferKind = cata $ \case
-- 
--     TVar k var -> do
--         pure (tVar k var)
-- 
--     TCon k con -> do
-- --        kind <- lookupKind con
-- --        traceShowM "****************"
-- --        traceShowM "***** TODO *****"
-- --        traceShowM "****************"
-- --        traceShowM kind
--         pure (tCon k con)
-- 
--     TArr ty1 ty2 -> do
--         t1 <- ty1 
--         t2 <- ty2 
-- --        runUnifyKinds kTyp (kindOf t1) -- >>= undefined --saveErrors
-- --        runUnifyKinds kTyp (kindOf t2) 
--         pure (tArr t1 t2)
-- 
--     TApp k ty1 ty2 -> do
--         t1 <- ty1 
--         t2 <- ty2 
-- --        runUnifyKinds (kArr (kindOf t2) k) (kindOf t1)
--         pure (tApp k t1 t2)
-- 
--     TRow label ty1 ty2 -> do
--         t1 <- ty1 
--         t2 <- ty2 
--         pure (tRow label t1 t2)
-- 
-- lookupKind
--   :: ( MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (a1, Substitution a2, c) m
--      , MonadSupply Name m, Substitutable Kind a2 ) 
--   => Name 
--   -> m Kind
-- lookupKind name = do
--     env <- asks getKindEnv
--     sub <- gets snd3
--     case Env.lookup name env of
--         Nothing -> do
--             -- TODO:
--             --insertErrors [UnboundTypeIdentifier name]
--             kVar . ("k" <>) <$> supply
--         Just kind ->
--             pure (apply sub kind)
-- 
-- -- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- 
-- inferAst
--   :: ( Monoid t
--      , Show t
--      , Typed t
--      , MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Ast t
--   -> m (Ast (TypeInfo [Error]))
-- inferAst (Ast expr) = do
--     e <- inferExprType expr
--     sub <- get
--     pure (simplifyPredicates <$> Ast (apply2 sub e))
-- 
-- inferExprType
--   :: ( Monoid t
--      , Show t
--      , Typed t
--      , MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => ProgExpr t
--   -> m (ProgExpr (TypeInfo [Error]))
-- inferExprType = cata $ \case
-- 
--     EVar _ var -> inferExprNode varExpr $ do
--         ty <- lookupScheme var >>= instantiate
--         unfiyWithNode ty
--         pure var
-- 
--     ECon _ con exprs -> inferExprNode (args2 conExpr) $ do
--         ty <- lookupScheme con >>= instantiate
--         es <- traverse exprNode exprs
--         t1 <- thisNodeType
--         ty ## foldr tArr t1 (typeOf <$> es)
--         pure (con, es)
-- 
--     ELit _ prim -> inferExprNode litExpr $ do
--         ty <- instantiate (primType prim)
--         unfiyWithNode ty
--         pure prim
-- 
--     EApp _ exprs -> inferExprNode appExpr $ do
--         es <- traverse exprNode exprs
--         case es of
--             [] -> pure ()
--             f:args -> do
--                 t1 <- thisNodeType
--                 f ## foldr tArr t1 (typeOf <$> args)
--         pure es
-- 
--     ELet _ (BPat _ pat) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
--         (p, vs) <- second nodeVars <$> listen (patternNode (inferPatternType pat))
--         e1 <- exprNode expr1
--         -- Unify bound variable with expression
--         p ## e1
-- 
--         schemes <- traverse (secondM generalize) vs
-- 
--         e2 <- exprNode (local (inTypeEnv (Env.inserts schemes)) expr2)
--         unfiyWithNode (typeOf e2)
-- 
--         name <- inferExprNode BPat $ do
--             unfiyWithNode (typeOf e1)
--             insertPredicates (exprPredicates e1 <> exprPredicates e2)
--             insertPredicates (patternPredicates p)
--             pure p
-- 
--         pure (name, e1, e2)
-- 
--     ELet _ (BFun _ f pats) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
--         (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPatternType) pats)
-- 
--         e1 <- exprNode (local (inTypeEnv (Env.inserts (toScheme <$$> vs))) expr1)
-- 
--         t1 <- newTVar 
--         t1 ## foldr tArr (typeOf e1) (typeOf <$> ps)
-- 
--         scheme <- generalize t1
--         e2 <- exprNode (local (inTypeEnv (Env.insert f scheme)) expr2)
--         unfiyWithNode (typeOf e2)
-- 
--         name <- inferExprNode (args2 BFun) $ do
--             unfiyWithNode t1
--             insertPredicates (exprPredicates e1 <> exprPredicates e2)
--             insertPredicates (patternPredicates =<< ps)
--             pure (f, ps)
-- 
--         pure (name, e1, e2)
-- 
--     EFix _ name expr1 expr2 -> inferExprNode (args3 fixExpr) $ do
--         t1 <- newTVar 
--         e1 <- exprNode (local (inTypeEnv (Env.insert name (toScheme t1))) expr1)
--         e1 ## (t1 :: Type) 
--         scheme <- generalize (typeOf e1)
--         e2 <- exprNode (local (inTypeEnv (Env.insert name scheme)) expr2)
--         unfiyWithNode (typeOf e2)
--         pure (name, e1, e2)
-- 
--     ELam _ pats expr -> inferExprNode (args2 lamExpr) $ do
--         (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPatternType) pats)
--         e1 <- exprNode (local (inTypeEnv (Env.inserts (toScheme <$$> vs))) expr)
--         unfiyWithNode (foldr tArr (typeOf e1) (typeOf <$> ps))
--         pure (ps, e1)
-- 
--     EIf _ expr1 expr2 expr3 -> inferExprNode (args3 ifExpr) $ do
--         e1 <- exprNode expr1
--         e2 <- exprNode expr2
--         e3 <- exprNode expr3
--         e1 ## (tBool :: Type)
--         e2 ## e3
--         unfiyWithNode (typeOf e2)
--         pure (e1, e2, e3)
-- 
--     EPat _ expr eqs -> inferExprNode (args2 patExpr) $ do
--         e1 <- exprNode expr
--         cs <- lift (traverse (inferClauseType (typeOf e1)) eqs)
--         insertPredicates (clausePredicates =<< cs)
--         -- Unify pattern clauses
--         forM_ cs $ \(Clause t p gs) -> do
--             forM_ gs (\(Guard _ e) -> unfiyWithNode (typeOf e))
--             unfiyWithNode (typeOf t)
--             unifyWith (typeOf e1) p
-- 
--         pure (e1, cs)
-- 
-- --        es1 <- traverse exprNode exprs
-- --        es2 <- lift (traverse (inferClauseType (typeOf <$> es1)) eqs)
-- --        insertPredicates (clausePredicates =<< es2)
-- --        -- Unify pattern clauses
-- --        forM_ es2 $ \(Clause t ps gs) -> do
-- --            forM_ gs (\(Guard _ e) -> unfiyWithNode (typeOf e))
-- --            unfiyWithNode (typeOf t)
-- --            forM_ (zip ps (typeOf <$> es1)) (uncurry unifyWith)
-- --
-- --        pure (es1, es2)
-- 
--     EFun _ eqs -> inferExprNode funExpr $ do
--         ty <- newTVar 
--         t1 <- thisNodeType
--         cs <- lift (traverse (inferClauseType t1) eqs)
--         insertPredicates (clausePredicates =<< cs)
--         -- Unify pattern clauses
--         forM_ cs $ \(Clause t p gs) -> do
--             forM_ gs (\(Guard _ e) -> t ## e >> t1 ## (ty `tArr` typeOf e))
--             p ## ty
-- 
--         pure cs
-- 
-- ----        ty <- newTVar 
-- ----        t1 <- newTVar 
-- ----        es <- lift (traverse (inferClauseType t1) eqs)
-- ----
-- ----        -- Unify return type with r.h.s. of arrow in clauses
-- ----        forM_ (clauseGuards =<< es) (\(Guard _ e) -> e ## (ty :: Type))
-- ----        -- Also unify return type with the type of clause itself
-- ----        forM_ es (unifyWith (ty :: Type) . clauseTag)
-- ----        -- Check pattern types
-- ----        forM_ (clausePatterns <$> es) (unifyWith t1)
-- ----
-- ----        insertPredicates (clausePredicates =<< es)
-- ------        unfiyWithNode t1
-- ----        pure es
-- 
-- --        ty <- newTVar 
-- --        ts <- newTVars (length ps)
-- --        es <- lift (traverse (inferClauseType ts) eqs)
-- --        -- Unify return type with r.h.s. of arrow in clauses
-- --        forM_ (clauseGuards =<< es) (\(Guard _ e) -> e ## (ty :: Type))
-- --        -- Also unify return type with the type of clause itself
-- --        forM_ es (unifyWith (ty :: Type) . clauseTag)
-- --        -- Check pattern types
-- --        forM_ (clausePatterns <$> es)
-- --            (\ps -> forM_ (zip ps ts) (uncurry unifyWith))
-- --
-- --        insertPredicates (clausePredicates =<< es)
-- --        unfiyWithNode (foldr tArr ty ts)
-- --        pure es
-- 
--     EOp1 _ op1 expr -> inferExprNode (args2 op1Expr) $ do
--         a <- exprNode expr
--         op <- inferOp1Type op1
--         t1 <- thisNodeType
--         op ## (typeOf a `tArr` t1)
--         pure (op, a)
-- 
--     EOp2 _ op2 expr1 expr2 -> inferExprNode (args3 op2Expr) $ do
--         a <- exprNode expr1
--         b <- exprNode expr2
--         op <- inferOp2Type op2
--         t1 <- thisNodeType
--         op ## (typeOf a `tArr` typeOf b `tArr` t1) 
--         pure (op, a, b)
-- 
--     ETuple _ exprs -> inferExprNode tupleExpr $ do
--         es <- traverse exprNode exprs
--         unfiyWithNode (tTuple (typeOf <$> es))
--         pure es
-- 
--     EList _ exprs -> inferExprNode listExpr $ do
--         es <- traverse exprNode exprs
--         t1 <- case es of
--             []    -> newTVar 
--             (e:_) -> pure (typeOf e)
-- 
--         -- Unify list elements' types
--         (_, node) <- listen (forM_ es (unifyWith t1))
--         when (nodeHasErrors node) $
--             insertErrors [ListElemUnficationError]
-- 
--         unfiyWithNode (tList t1)
--         pure es
-- 
--     ERow _ label expr row -> inferExprNode (args3 rowExpr) $ do
--         e <- exprNode expr
--         r <- exprNode row
-- 
--         unfiyWithNode (tRow label (typeOf e) (typeOf r))
--         pure (label, e, r)
-- 
--     EAnn t expr -> do
--         e <- expr
--         void $ inferNodeType t (unfiyWithNode (typeOf e))
--         pure e
-- 
-- --flattenRow :: Type -> Type
-- --flattenRow = cata $ \case
-- --    TVar k var -> tVar k var
-- --    TCon k con -> tCon k con
-- --    TArr a b   -> tArr a b
-- --    TApp k (Fix (TCon _ "{*}")) b -> undefined
-- --    TApp k a b -> undefined
-- 
-- --    ERecord _ row -> inferExprNode recordExpr $ do
-- --        fs <- inferRowType row
-- --        traceShowM fs
-- ----        unfiyWithNode (tApp kTyp (tCon (kArr kRow kTyp) "#") (typeOf fs))
-- --        pure fs
-- 
-- --inferRowType
-- --  :: ( MonadSupply Name m
-- --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
-- --     , MonadState (Substitution Type, Substitution Kind, Context) m )
-- --  => (Name, m (ProgExpr (TypeInfo [Error])))
-- --  -> WriterT Node m (Name, ProgExpr (TypeInfo [Error]))
-- --inferRowType (label, expr) = do
-- --    e <- lift expr
-- --    insertPredicates (exprPredicates e)
-- --    pure (label, e)
-- 
-- --inferRowType 
-- --  :: ( MonadSupply Name m
-- --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
-- --     , MonadState (Substitution Type, Substitution Kind, Context) m )
-- --  => m (ProgExpr (TypeInfo [Error]))
-- --  -> WriterT Node m (ProgExpr (TypeInfo [Error]))
-- --inferRowType expr = do
-- --    e <- lift expr
-- --    pure e
-- 
-- inferPatternType
--   :: ( Typed t
--      , MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => ProgPattern t
--   -> m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
-- inferPatternType = cata $ \case
-- 
--     PVar _ var -> inferPatternNode varPat $ do
--         t <- thisNodeType
--         tellVars [(var, t)]
--         pure var
-- 
--     PCon _ con pats -> inferPatternNode (args2 conPat) $ do
--         lookupConstructor con >>= \case
--             Nothing -> pure ()
--             Just (_, arity) -> do
--                 -- The number of arguments must match arity of constructor
--                 when (arity /= length pats) $
--                     insertErrors [ConstructorPatternArityMismatch con arity (length pats)]
-- 
--         ty <- lookupScheme con >>= instantiate
--         ps <- traverse patternNode pats
-- 
--         t1 <- thisNodeType
--         (_, node) <- listen (ty ## foldr tArr t1 (typeOf <$> ps))
--         when (nodeHasErrors node) $
--             insertErrors [ConstructorPatternTypeMismatch con]
-- 
--         pure (con, ps)
-- 
--     PLit _ prim -> inferPatternNode litPat $ do
--         t <- instantiate (primType prim)
--         unfiyWithNode t
--         pure prim
-- 
--     PAs _ var pat -> inferPatternNode (args2 asPat) $ do
--         p <- patternNode pat
--         t <- thisNodeType
--         tellVars [(var, t)]
--         unfiyWithNode (typeOf p)
--         pure (var, p)
-- 
--     POr _ pat1 pat2 -> inferPatternNode (args2 orPat) $ do
--         p1 <- patternNode pat1
--         p2 <- patternNode pat2
--         unfiyWithNode (typeOf p1)
--         unfiyWithNode (typeOf p2)
--         pure (p1, p2)
-- 
--     PAny _ -> inferPatternNode (args0 anyPat) $ pure ()
-- 
--     PTuple t pats -> inferPatternNode tuplePat $ do
--         ps <- traverse patternNode pats
--         unfiyWithNode (tTuple (typeOf <$> ps))
--         pure ps
-- 
--     PList t pats -> inferPatternNode listPat $ do
--         ps <- traverse patternNode pats
--         t1 <- case ps of
--             []    -> newTVar 
--             (p:_) -> pure (typeOf p)
-- 
--         -- Unify list elements' types
--         (_, node) <- listen (forM_ ps (unifyWith t1))
--         when (nodeHasErrors node) $
--             insertErrors [ListPatternElemUnficationError]
-- 
--         unfiyWithNode (tList t1)
--         pure ps
-- 
--     PRow _ label pat row -> inferPatternNode (args3 rowPat) $ do
--         p <- patternNode pat
--         r <- patternNode row
-- 
--         unfiyWithNode (tRow label (typeOf p) (typeOf r))
--         pure (label, p, r)
-- 
--     PAnn t pat -> do
--         p <- pat
--         void $ inferNodeType t (unfiyWithNode (typeOf (fst p)))
--         pure p
-- 
-- patternNode
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
--   -> WriterT Node m (ProgPattern (TypeInfo [Error]))
-- patternNode pat = do
--     (p, vs) <- lift pat
--     insertPredicates (patternPredicates p)
--     tellVars vs
--     pure p
-- 
-- exprNode
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => m (ProgExpr (TypeInfo [Error]))
--   -> WriterT Node m (ProgExpr (TypeInfo [Error]))
-- exprNode expr = do
--     e <- lift expr
--     insertPredicates (exprPredicates e)
--     pure e
-- 
-- thisNodeType
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => WriterT Node m Type
-- thisNodeType = do
--     t <- newTVar 
--     unfiyWithNode t
--     pure t
-- 
-- opType
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => (TypeInfo [Error] -> a)
--   -> Scheme
--   -> WriterT Node m a
-- opType op scheme = do
--     (t, (_, _, ps, es)) <- listen (instantiate scheme)
--     pure (op (TypeInfo es t ps))
-- 
-- inferOp1Type
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Op1 t
--   -> WriterT Node m (Op1 (TypeInfo [Error]))
-- inferOp1Type = \case
--     ONeg _ -> opType ONeg (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0))
--     ONot _ -> opType ONot (Forall [] [] (tBool `tArr` tBool))
-- 
-- inferOp2Type
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Op2 t
--   -> WriterT Node m (Op2 (TypeInfo [Error]))
-- inferOp2Type = \case
--     OEq  _ -> opType OEq  (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
--     ONeq _ -> opType ONeq (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
--     OAdd _ -> opType OAdd (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
--     OMul _ -> opType OMul (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
--     OSub _ -> opType OSub (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
--     OAnd _ -> opType OAnd (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
--     OOr  _ -> opType OOr  (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
--     OLt  _ -> opType OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
--     OGt  _ -> opType OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
--     OLte _ -> opType OLte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
--     OGte _ -> opType OGte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
-- 
-- inferClauseType
--   :: ( Monoid t
--      , Show t
--      , Typed t
--      , MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Type
--   -> Clause t (ProgPattern t) (m (ProgExpr (TypeInfo [Error])))
--   -> m (ProgClause (TypeInfo [Error]))
-- inferClauseType ty eq@(Clause _ pat _) = inferExprNode (args2 Clause) $ do
--     (p, (_, vs, _, _)) <- listen (patternNode (inferPatternType pat)) 
--     let schemes = toScheme <$$> vs
--         Clause _ _ guards = local (inTypeEnv (Env.inserts schemes)) <$> eq
--         (iffs, es) = unzip (guardToPair <$> guards)
--     -- Iff-conditions must be Bool
--     forM_ (concat iffs) unifyIffCondition
--     gs <- traverse inferGuard guards
--     pure (p, gs)
-- 
-- --inferClauseType
-- --  :: ( Monoid t
-- --     , Show t
-- --     , MonadSupply Name m
-- --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
-- --     , MonadState (Substitution Type, Substitution Kind, Context) m )
-- --  => [Type]
-- --  -> Clause t (ProgPattern t) (m (ProgExpr (TypeInfo [Error])))
-- --  -> m (ProgClause (TypeInfo [Error]))
-- --inferClauseType = undefined
-- --inferClauseType tys eq@(Clause _ pats _) = inferExprNode (args2 Clause) $ do
-- --    (ps, (_, vs, _, _)) <- listen (traverse (patternNode . inferPatternType) pats)
-- --    let schemes = toScheme <$$> vs
-- --        Clause _ _ guards = local (inTypeEnv (Env.inserts schemes)) <$> eq
-- --        (iffs, es) = unzip (guardToPair <$> guards)
-- --    -- Conditions must be Bool
-- --    forM_ (concat iffs) unifyIffCondition
-- --    gs <- traverse inferGuard guards
-- --    pure (ps, gs)
-- 
-- inferGuard
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Guard (m (ProgExpr (TypeInfo [Error])))
--   -> WriterT Node m (Guard (ProgExpr (TypeInfo [Error])))
-- inferGuard (Guard es e) = Guard <$> traverse exprNode es <*> exprNode e
-- 
-- unifyIffCondition
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => m (ProgExpr (TypeInfo [Error]))
--   -> WriterT Node m ()
-- unifyIffCondition expr = do
--     e <- lift expr
--     (_, node) <- listen (e ## (tBool :: Type))
--     when (nodeHasErrors node) $
--         insertErrors [GuardConditionNotABool]
-- 
-- primType :: Prim -> Scheme
-- primType = \case
--     TUnit      -> Forall [] [] tUnit
--     TBool{}    -> Forall [] [] tBool
--     TChar{}    -> Forall [] [] tChar
--     TString{}  -> Forall [] [] tString
--     TInt{}     -> Forall [kTyp] [InClass "Num" 0] (tGen 0)
--     TInteger{} -> Forall [kTyp] [InClass "Num" 0] (tGen 0)
--     TFloat{}   -> Forall [kTyp] [InClass "Fractional" 0] (tGen 0)
--     TDouble{}  -> Forall [kTyp] [InClass "Fractional" 0] (tGen 0)
-- 
-- -- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- 
-- newTVar :: (MonadSupply Name m) => m (TypeT a)
-- newTVar = do
--     k <- ("k" <>) <$> supply
--     t <- ("a" <>) <$> supply
--     pure (tVar (kVar k) t)
-- 
-- newTVars :: (MonadSupply Name m) => Int -> m [TypeT a]
-- newTVars = flip replicateM newTVar
-- 
-- instantiate
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Scheme
--   -> WriterT Node m Type
-- instantiate (Forall kinds preds ty) = do
--     names <- ("a" <>) <$$> supplies (length kinds)
--     let ts = zipWith tVar kinds names
--         (pairs, ps) = unzip (fn <$> preds)
--         fn p@(InClass tc ix) =
--             ( (names !! ix, Set.singleton tc)
--             , fromPolytype ts <$> (tGen <$> p) )
--     modify (third3 (`insertAll` pairs))
--     insertPredicates ps
--     pure (fromPolytype ts ty)
-- 
-- generalize
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Type
--   -> m Scheme
-- generalize ty = do
--     env <- askTypeEnv
--     sub <- get
--     let typ = apply2 sub ty
--         frees = fst <$> free (apply (fst3 sub) env)
--         (vs, ks) = unzip $ filter ((`notElem` frees) . fst) (typeVars typ)
--         ixd = Map.fromList (zip vs [0..])
--     ps <- lookupPredicates vs
--     pure (Forall ks (toPred ixd <$> ps) (apply (Sub (tGen <$> ixd)) (toPolytype typ)))
--   where
--     toPred map (var, tc) = InClass tc (fromJust (Map.lookup var map))
-- 
-- insertAll :: Context -> [(Name, Set Name)] -> Context
-- insertAll = foldr (uncurry (Env.insertWith Set.union))
-- 
-- lookupConstructor
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Name
--   -> WriterT Node m (Maybe (Set Name, Int))
-- lookupConstructor con = do
--     env <- asks getConstructorEnv
--     let info = Env.lookup con env
--     when (isNothing info) (insertErrors [MissingDataConstructor con])
--     pure info
-- 
-- lookupScheme
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Name
--   -> WriterT Node m Scheme
-- lookupScheme name = do
--     env <- asks getTypeEnv
--     sub <- gets fst3
--     case Env.lookup name env of
--         Nothing -> do
--             insertErrors [UnboundTypeIdentifier name]
--             toScheme <$> newTVar 
--         Just ty ->
--             pure (apply sub ty)
-- 
-- lookupPredicates
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => [Name]
--   -> m [(Name, Name)]
-- lookupPredicates vars = do
--     env <- gets thd3
--     pure [(v, tc) | v <- vars, tc <- Set.toList (Env.findWithDefault mempty v env)]
-- 
-- propagateClasses
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m
--      , MonadError Error m )
--   => Type
--   -> Set Name
--   -> m ()
-- propagateClasses (Fix (TVar _ var)) ps
--     | Set.null ps = pure ()
--     | otherwise   = modify (third3 (Env.insertWith Set.union var ps))
-- propagateClasses ty ps =
--     forM_ ps $ \name -> do
--         env <- asks getClassEnv
--         ClassInfo{ classSuper = preds } <- lookupClassInstance name ty env
--         sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]
-- 
-- -- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- 
-- args0 :: (TypeInfo [Error] -> a) -> TypeInfo [Error] -> () -> a
-- args0 f ti () = f ti
-- 
-- args2 :: (TypeInfo [Error] -> t1 -> t2 -> a) -> TypeInfo [Error] -> (t1, t2) -> a
-- args2 f ti (a, b) = f ti a b
-- 
-- args3 :: (TypeInfo [Error] -> t1 -> t2 -> t3 -> a) -> TypeInfo [Error] -> (t1, t2, t3) -> a
-- args3 f ti (a, b, c) = f ti a b c
-- 
-- inferPatternNode
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => (TypeInfo [Error] -> t -> a)
--   -> WriterT Node m t
--   -> m (a, [(Name, Type)])
-- inferPatternNode c f = do
--     newTy <- newTVar 
--     (a, ti, vs) <- inferNodeType newTy f
--     pure (c ti a, vs)
-- 
-- inferExprNode
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => (TypeInfo [Error] -> t1 -> a)
--   -> WriterT Node m t1
--   -> m a
-- inferExprNode c f = do
--     newTy <- newTVar 
--     (a, ti, _) <- inferNodeType newTy f
--     pure (c ti a)
-- 
-- -- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- 
-- -- Type class instances
-- 
-- instance (Typed t) => Typed (ProgExpr t) where
--     typeOf = typeOf . exprTag
-- 
-- instance (Typed t) => Typed (ProgPattern t) where
--     typeOf = typeOf . patternTag
-- 
-- instance (Typed t) => Typed (Op1 t) where
--     typeOf = typeOf . op1Tag
-- 
-- instance (Typed t) => Typed (Op2 t) where
--     typeOf = typeOf . op2Tag
-- 
-- instance (Typed t) => Typed (Ast t) where
--     typeOf = typeOf . astTag
-- 
-- -- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- 
-- type Node = 
--     ( List Type           -- Types that unify with the node's type
--     , List (Name, Type)   -- Pattern variables
--     , List Predicate      -- Class predicates
--     , List Error          -- Errors
--     )
-- 
-- unfiyWithNode :: (MonadWriter Node m) => Type -> m ()
-- unfiyWithNode ty = tell ([ty], mempty, mempty, mempty)
-- 
-- tellVars :: (MonadWriter Node m) => [(Name, Type)] -> m ()
-- tellVars vs = tell (mempty, vs, mempty, mempty)
-- 
-- insertPredicates :: (MonadWriter Node m) => [Predicate] -> m ()
-- insertPredicates ps = tell (mempty, mempty, ps, mempty)
-- 
-- insertErrors :: (MonadWriter Node m) => [Error] -> m ()
-- insertErrors es = tell (mempty, mempty, mempty, es)
-- 
-- nodeHasErrors :: Node -> Bool
-- nodeHasErrors (_, _, _, es) = not (Prelude.null es)
-- 
-- nodeVars :: Node -> [(Name, Type)]
-- nodeVars (_, vs, _, _) = vs
-- 
-- inferNodeType
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Type
--   -> WriterT Node m a
--   -> m (a, TypeInfo [Error], [(Name, Type)])
-- inferNodeType t w = do
--     (a, (ts, vs, ps, err)) <- runWriterT w
--     errs <- lefts <$> mapM (runUnify t) ts
--     sub <- gets fst3
--     t' <- inferKind (apply sub t)
--     pure (a, TypeInfo (err <> errs) t' (nub (apply sub ps)), vs)

-- runUnify
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m
--      , Typed a
--      , Typed b )
--   => a
--   -> b
--   -> m (Either Error ())
-- runUnify = runExceptT <$$> unifyTyped
--   where
--     unifyTyped a b = do
--         let t1 = typeOf a
--             t2 = typeOf b
--         (typeSub, kindSub) <- applyAnd unifyTypes (gets fst3) CannotUnify t1 t2
--         modify (first3 (typeSub <>))
--         modify (second3 (kindSub <>))
-- --        runUnifyKinds (kindOf t1) (kindOf t2)
--         forM_ (Map.toList (getSub typeSub)) (uncurry propagate)
--       where
--         propagate tv ty = do
--             env <- gets thd3
--             propagateClasses ty (fromMaybe mempty (Env.lookup tv env))
-- 
-- runUnifyKinds
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m )
--   => Kind
--   -> Kind
--   -> m (Either Error ())
-- runUnifyKinds = runExceptT <$$> (\k1 k2 -> do
--     sub <- applyAnd unifyKinds (gets snd3) KindMismatch k1 k2
--     modify (second3 (sub <>)))
-- 
-- --applyAnd
-- --  :: ( Substitutable t1 a
-- --     , Substitutable t2 a
-- --     , MonadError e m 
-- --     , MonadSupply Name m
-- --     )
-- --  => (t1 -> t2 -> Except t3 sub)
-- --  -> m (Substitution a)
-- --  -> (t1 -> t2 -> t3 -> e)
-- --  -> t1
-- --  -> t2
-- --  -> m sub
-- applyAnd unify getSub toError t1 t2 = do
--     sub <- getSub
--     runExceptT (unify (apply sub t1) (apply sub t2)) >>= \case
--         Left err  -> throwError (toError t1 t2 err)
--         Right sub -> pure sub
-- 
-- --unifiedT
-- --  :: ( MonadSupply Name m
-- --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
-- --     , MonadState (Substitution Type, Substitution Kind, Context) m
-- --     , MonadError Error m )
-- --  => Type
-- --  -> Type
-- --  -> m (Substitution Type)
-- --unifiedT =  
-- 
-- -- unifiedK k1 = applyAnd unifyKinds KindMismatch snd3 k1 
-- 
-- --unifiedT
-- --  :: ( MonadSupply Name m
-- --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
-- --     , MonadState (Substitution Type, Substitution Kind, Context) m
-- --     , MonadError Error m )
-- --  => Type
-- --  -> Type
-- --  -> m (Substitution Type)
-- --unifiedT t1 t2 = do
-- --    sub1 <- gets fst3
-- --    case runExcept (unifyTypes (apply sub1 t1) (apply sub1 t2)) of
-- --        Left err  -> throwError (CannotUnify t1 t2 err)
-- --        Right sub -> pure sub
-- 
-- --unifiedTK
-- --  :: ( MonadSupply Name m
-- --     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
-- --     , MonadState (Substitution Type, Substitution Kind, Context) m
-- --     , MonadError Error m )
-- --  => Kind
-- --  -> Kind
-- --  -> m (Substitution Kind)
-- --unifiedTK k1 k2 = do
-- --    sub1 <- gets snd3
-- --    case runExcept (unifyKinds (apply sub1 k1) (apply sub1 k2)) of
-- --        Left err  -> throwError (KindMismatch k1 k2 err)
-- --        Right sub -> pure sub
-- 
-- unifyWith
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m
--      , Typed a
--      , Typed b
--      , Substitutable a Type
--      , Substitutable b Type )
--   => a
--   -> b
--   -> WriterT Node m ()
-- unifyWith a b = do
--     sub <- gets fst3
--     tub <- gets snd3
--     let t1 = typeOf (apply sub a)
--         t2 = typeOf (apply sub b)
--     runUnify t1 t2 >>= saveErrors
-- --    runUnifyKinds (kindOf t1) (kindOf t2) >>= saveErrors
--   where
--     saveErrors = whenLeft (insertErrors . pure)
-- 
-- (##)
--   :: ( MonadSupply Name m
--      , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--      , MonadState (Substitution Type, Substitution Kind, Context) m
--      , Typed a
--      , Typed b
--      , Substitutable a Type
--      , Substitutable b Type )
--   => a
--   -> b
--   -> WriterT Node m ()
-- (##) = unifyWith

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Monad transformer stack

type InferState   = StateT (Substitution Type, Substitution Kind, Context)
type InferReader  = ReaderT (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
type InferSupply  = SupplyT Name
type InferStack a = InferReader (InferState (InferSupply (MaybeT a)))

runInferState :: (Monad m) => Context -> InferState m a -> m (a, (Substitution Type, Substitution Kind, Context))
runInferState context = flip runStateT (mempty, mempty, context)

runInferReader :: (Monad m) => ClassEnv -> TypeEnv -> KindEnv -> ConstructorEnv -> InferReader m r -> m r
runInferReader e1 e2 e3 e4 = flip runReaderT (e1, e2, e3, e4)

runInferSupply :: (Monad m) => InferSupply m a -> m a
runInferSupply = flip evalSupplyT (numSupply "")

runInferT
  :: (Monad m) 
  => Context
  -> ClassEnv
  -> TypeEnv
  -> KindEnv
  -> ConstructorEnv
  -> InferStack m a
  -> m (a, Substitution Type, Substitution Kind, Context)
runInferT context classEnv typeEnv kindEnv constructorEnv =
    runInferReader classEnv typeEnv kindEnv constructorEnv
    >>> runInferState context
    >>> runInferSupply
    >>> runMaybeT
    >>> fmap (to <$>)
    >>> fmap fromJust

runInfer
  :: Context
  -> ClassEnv
  -> TypeEnv
  -> KindEnv
  -> ConstructorEnv
  -> InferStack Identity a
  -> (a, Substitution Type, Substitution Kind, Context)
runInfer context classEnv typeEnv kindEnv constructorEnv = 
    runIdentity . runInferT context classEnv typeEnv kindEnv constructorEnv
