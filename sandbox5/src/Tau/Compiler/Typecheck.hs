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
import Tau.Compiler.Substitute
import Tau.Compiler.Unify
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

inferKind 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> m Type
inferKind = cata $ \case

    TVar k var -> do
        pure (tVar k var)

    TCon k con -> do
        pure (tCon k con)

    TArr ty1 ty2 -> do
        t1 <- ty1 
        t2 <- ty2 
        unifyTypeKinds kTyp (kindOf t1) 
        unifyTypeKinds kTyp (kindOf t2) 
        pure (tArr t1 t2)

    TApp k ty1 ty2 -> do
        t1 <- ty1 
        t2 <- ty2 
        unifyTypeKinds (kArr (kindOf t2) k) (kindOf t1)
        pure (tApp k t1 t2)

--lookupKind
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Substitution Kind, Context) m )
--  => Name
--  -> m (Maybe Kind)
--lookupKind name = do
--    env <- asks getKindEnv
--    sub <- gets snd3
--    pure (apply sub <$> Env.lookup name env)
--
--runUnifyKinds
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Substitution Kind, Context) m )
--  => Type
--  -> Type
--  -> m (Either Error ())
--runUnifyKinds = undefined
----runUnify = runExceptT <$$> unifyTyped
----  where
----    unifyTyped a b = do
----        sub <- unifiedT (typeOf a) (typeOf b)
----        modify (first3 (sub <>))
----        forM_ (Map.toList (getSub sub)) (uncurry propagate)
----      where
----        propagate tv ty = do
----            env <- gets thd3
----            propagateClasses ty (fromMaybe mempty (Env.lookup tv env))
--
--xxx :: (Monad m) => Type -> Type -> m a
--xxx t1 t2 = do
--    --sub <- unifyTypeKinds (kindOf t1) (kindOf t2)
--    undefined
--
--    pure $ case Env.lookup name env of
--        Nothing -> 
--            Nothing
--        Just kind ->
--            Just (apply sub kind)

--lookupScheme name = do
--    env <- asks getTypeEnv
--    sub <- gets fst
--    case Env.lookup name env of
--        Nothing -> do
--            insertErrors [UnboundTypeIdentifier name]
--            toScheme <$> newTVar 
--        Just ty ->
--            pure (apply sub ty)

unifyTypeKinds = undefined

--        Right sub2 -> do
--            modify (second3 (sub2 <>))
--            undefined
--            --pure sub

--unifiedT
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Substitution Kind, Context) m
--     , MonadError Error m )
--  => Type
--  -> Type
--  -> m (Substitution Type)
--unifiedT t1 t2 = do
--    sub1 <- gets fst3
--    case runExcept (unifyTypes (apply sub1 t1) (apply sub1 t2)) of
--        Left err  -> throwError (CannotUnify t1 t2 err)
--        Right sub -> pure sub
--

--runUnifyKinds
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Context) m
--     , Typed a
--     , Typed b )
--  => a
--  -> b
--  -> m (Either Error ())
--runUnifyKinds = runExceptT <$$> unifyTyped
--  where
--    unifyTyped a b = do
--        sub <- unifiedT (typeOf a) (typeOf b)
--        modify (first (sub <>))
--        forM_ (Map.toList (getSub sub)) (uncurry propagate)
--      where
--        propagate tv ty = do
--            env <- gets snd
--            propagateClasses ty (fromMaybe mempty (Env.lookup tv env))
--unifyTypeKinds
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Kind, Context) m )
--  => Kind
--  -> Kind
--  -> m ()
--unifyTypeKinds k1 k2 = do
--    sub1 <- gets fst
--    case runExcept (unifyKinds (apply sub1 k1) (apply sub1 k2)) of
--        Left err  -> throwError (KindMismatch k1 k2 err)
--        Right sub2 -> 
--            modify (first (sub2 <>))
--            --pure sub

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

inferAst
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Ast t
  -> m (Ast (TypeInfo [Error]))
inferAst (Ast expr) = do
    e <- inferExprType expr
    sub <- gets fst3
    pure (simplifyPredicates <$> Ast (apply sub e))

inferExprType
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgExpr t
  -> m (ProgExpr (TypeInfo [Error]))
inferExprType = cata $ \case

    EVar _ var -> inferExprNode varExpr $ do
        ty <- lookupScheme var >>= instantiate
        unfiyWithNode ty
        pure var

    ECon _ con exprs -> inferExprNode (args2 conExpr) $ do
        ty <- lookupScheme con >>= instantiate
        es <- traverse exprNode exprs
        t1 <- thisNodeType
        ty ## foldr tArr t1 (typeOf <$> es)
        pure (con, es)

    ELit _ prim -> inferExprNode litExpr $ do
        ty <- instantiate (primType prim)
        unfiyWithNode ty
        pure prim

    EApp _ exprs -> inferExprNode appExpr $ do
        es <- traverse exprNode exprs
        case es of
            [] -> pure ()
            f:args -> do
                t1 <- thisNodeType
                f ## foldr tArr t1 (typeOf <$> args)
        pure es

    ELet _ (BLet _ pat) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
        undefined

--    ELet _ (BLet _ pat) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
--        (p, vs) <- second nodeVars <$> listen (patternNode (inferPattern pat))
--
--        e1 <- exprNode expr1
--        -- Unify bound variable with expression
--        p ## e1
--
--        schemes <- traverse (secondM generalize) vs
--        e2 <- exprNode (local (onTypeEnv (Env.inserts schemes)) expr2)
--        unfiyWithNode (typeOf e2)
--
--        name <- inferExprNode BLet $ do
--            unfiyWithNode (typeOf e1)
--            insertPredicates (exprPredicates e1 <> exprPredicates e2)
--            insertPredicates (patternPredicates p)
--            pure p
--
--        pure (name, e1, e2)

    ELet _ (BFun _ f pats) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
        undefined

--    ELet _ (BFun _ f pats) expr1 expr2 -> inferExprNode (args3 letExpr) $ do
--        (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPattern) pats)
--
--        e1 <- exprNode (local (onTypeEnv (Env.inserts (toScheme <$$> vs))) expr1)
--
--        t1 <- newTVar kHole
--        t1 ## foldr tArr (typeOf e1) (typeOf <$> ps)
--
--        scheme <- generalize t1
--        e2 <- exprNode (local (onTypeEnv (Env.insert f scheme)) expr2)
--        unfiyWithNode (typeOf e2)
--
--        name <- inferExprNode (args2 BFun) $ do
--            unfiyWithNode t1
--            insertPredicates (exprPredicates e1 <> exprPredicates e2)
--            insertPredicates (patternPredicates =<< ps)
--            pure (f, ps)
--
--        pure (name, e1, e2)

    EFix _ name expr1 expr2 -> inferExprNode (args3 fixExpr) $ do
        undefined

--    EFix _ name expr1 expr2 -> inferExprNode (args3 fixExpr) $ do
--        t1 <- newTVar kHole
--        e1 <- exprNode (local (onTypeEnv (Env.insert name (toScheme t1))) expr1)
--        e1 ## (t1 :: Type) 
--        scheme <- generalize (typeOf e1)
--        e2 <- exprNode (local (onTypeEnv (Env.insert name scheme)) expr2)
--        unfiyWithNode (typeOf e2)
--        pure (name, e1, e2)

    ELam _ pats expr -> inferExprNode (args2 lamExpr) $ do
        (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPatternType) pats)
        e1 <- exprNode (local (onTypeEnv (Env.inserts (toScheme <$$> vs))) expr)
        pure (ps, e1)

--    ELam _ pats expr -> inferExprNode (args2 lamExpr) $ do
--        (ps, vs) <- second nodeVars <$> listen (traverse (patternNode . inferPattern) pats)
--        e1 <- exprNode (local (onTypeEnv (Env.inserts (toScheme <$$> vs))) expr)
--        unfiyWithNode (foldr tArr (typeOf e1) (typeOf <$> ps))
--        pure (ps, e1)

    EIf _ expr1 expr2 expr3 -> inferExprNode (args3 ifExpr) $ do
        e1 <- exprNode expr1
        e2 <- exprNode expr2
        e3 <- exprNode expr3
        pure (e1, e2, e3)

--    EIf _ expr1 expr2 expr3 -> inferExprNode (args3 ifExpr) $ do
--        e1 <- exprNode expr1
--        e2 <- exprNode expr2
--        e3 <- exprNode expr3
--        e1 ## (tBool :: Type)
--        e2 ## e3
--        unfiyWithNode (typeOf e2)
--        pure (e1, e2, e3)

    EPat _ exprs eqs -> inferExprNode (args2 patExpr) $ do
        es1 <- traverse exprNode exprs
        es2 <- lift (traverse (inferClauseType (typeOf <$> es1)) eqs)
        pure (es1, es2)

--    EPat _ exprs eqs -> inferExprNode (args2 patExpr) $ do
--        es1 <- traverse exprNode exprs
--        es2 <- lift (traverse (inferClause (typeOf <$> es1)) eqs)
--        insertPredicates (clausePredicates =<< es2)
--        -- Unify pattern clauses
--        forM_ es2 $ \(Clause t ps gs) -> do
--            forM_ gs (\(Guard _ e) -> unfiyWithNode (typeOf e))
--            unfiyWithNode (typeOf t)
--            forM_ (zip ps (typeOf <$> es1)) (uncurry unifyWith)
--
--        pure (es1, es2)

    EFun _ eqs@(Clause _ ps _:_) -> inferExprNode funExpr $ do
        ts <- newTVars (length ps)
        es <- lift (traverse (inferClauseType ts) eqs)
        pure es

--    EFun _ eqs@(Clause _ ps _:_) -> inferExprNode funExpr $ do
--        ty <- newTVar 
--        ts <- newTVars (length ps)
--        es <- lift (traverse (inferClause ts) eqs)
--        -- Unify return type with r.h.s. of arrow in clauses
--        forM_ (clauseGuards =<< es) (\(Guard _ e) -> e ## (ty :: Type))
--        -- Also unify return type with the type of clause itself
--        forM_ es (unifyWith (ty :: Type) . clauseTag)
--        -- Check pattern types
--        forM_ (clausePatterns <$> es)
--            (\ps -> forM_ (zip ps ts) (uncurry unifyWith))
--
--        insertPredicates (clausePredicates =<< es)
--        unfiyWithNode (foldr tArr ty ts)
--        pure es

    EOp1 _ op1 expr -> inferExprNode (args2 op1Expr) $ do
        a <- exprNode expr
        op <- inferOp1Type op1
        pure (op, a)

--    EOp1 _ op1 expr -> inferExprNode (args2 op1Expr) $ do
--        a <- exprNode expr
--        op <- inferOp1 op1
--        t1 <- thisNodeType
--        op ## (typeOf a `tArr` t1)
--        pure (op, a)

    EOp2 _ op2 expr1 expr2 -> inferExprNode (args3 op2Expr) $ do
        a <- exprNode expr1
        b <- exprNode expr2
        op <- inferOp2Type op2
        pure (op, a, b)

--    EOp2 _ op2 expr1 expr2 -> inferExprNode (args3 op2Expr) $ do
--        a <- exprNode expr1
--        b <- exprNode expr2
--        op <- inferOp2 op2
--        t1 <- thisNodeType
--        op ## (typeOf a `tArr` typeOf b `tArr` t1) 
--        pure (op, a, b)

    ETuple _ exprs -> inferExprNode tupleExpr $ do
        es <- traverse exprNode exprs
        pure es

--    ETuple _ exprs -> inferExprNode tupleExpr $ do
--        es <- traverse exprNode exprs
--        unfiyWithNode (tTuple (typeOf <$> es))
--        pure es

    EList _ exprs -> inferExprNode listExpr $ do
        es <- traverse exprNode exprs
        pure es

--    EList _ exprs -> inferExprNode listExpr $ do
--        es <- traverse exprNode exprs
--        t1 <- case es of
--            []    -> newTVar kHole
--            (e:_) -> pure (typeOf e)
--
--        -- Unify list elements' types
--        (_, node) <- listen (forM_ es (unifyWith t1))
--        when (nodeHasErrors node) $
--            insertErrors [ListElemUnficationError]
--
--        unfiyWithNode (tList t1)
--        pure es
--
--    ERecord _ row -> inferExprNode recordExpr $ do
--        fs <- traverse exprNode row
--        unfiyWithNode (tRecord (rowToType (typeOf <$> fs)))
--        pure fs

inferPatternType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgPattern t
  -> m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
inferPatternType = cata $ \case

    PVar _ var -> inferPatternNode varPat $ do
        pure var

--        t <- thisNodeType
--        tellVars [(var, t)]
--        pure var

    PCon _ con pats -> inferPatternNode (args2 conPat) $ do
        ps <- traverse patternNode pats
        pure (con, ps)

--        lookupConstructor con >>= \case
--            Nothing -> pure ()
--            Just (_, arity) -> do
--                -- The number of arguments must match arity of constructor
--                when (arity /= length pats) $
--                    insertErrors [ConstructorPatternArityMismatch con arity (length pats)]
--
--        ty <- lookupScheme con >>= instantiate
--        ps <- traverse patternNode pats
--
--        t1 <- thisNodeType
--        (_, node) <- listen (ty ## foldr tArr t1 (typeOf <$> ps))
--        when (nodeHasErrors node) $
--            insertErrors [ConstructorPatternTypeMismatch con]
--
--        pure (con, ps)

    PLit _ prim -> inferPatternNode litPat $ do
        pure prim

--    PLit _ prim -> inferPatternNode litPat $ do
--        t <- instantiate (primType prim)
--        unfiyWithNode t
--        pure prim

    PAs _ var pat -> inferPatternNode (args2 asPat) $ do
        p <- patternNode pat
        pure (var, p)

--    PAs _ var pat -> inferPatternNode (args2 asPat) $ do
--        p <- patternNode pat
--        t <- thisNodeType
--        tellVars [(var, t)]
--        unfiyWithNode (typeOf p)
--        pure (var, p)

    POr _ pat1 pat2 -> inferPatternNode (args2 orPat) $ do
        p1 <- patternNode pat1
        p2 <- patternNode pat2
        pure (p1, p2)

--    POr _ pat1 pat2 -> inferPatternNode (args2 orPat) $ do
--        p1 <- patternNode pat1
--        p2 <- patternNode pat2
--        unfiyWithNode (typeOf p1)
--        unfiyWithNode (typeOf p2)
--        pure (p1, p2)

    PAny _ ->
        inferPatternNode (args0 anyPat) $ pure ()

    PTuple t pats -> inferPatternNode tuplePat $ do
        ps <- traverse patternNode pats
        pure ps

--    PTuple t pats -> inferPatternNode tuplePat $ do
--        ps <- traverse patternNode pats
--        unfiyWithNode (tTuple (typeOf <$> ps))
--        pure ps

    PList t pats -> inferPatternNode listPat $ do
        ps <- traverse patternNode pats
        pure ps

--    PList t pats -> inferPatternNode listPat $ do
--        ps <- traverse patternNode pats
--        t1 <- case ps of
--            []    -> newTVar kHole
--            (p:_) -> pure (typeOf p)
--
--        -- Unify list elements' types
--        (_, node) <- listen (forM_ ps (unifyWith t1))
--        when (nodeHasErrors node) $
--            insertErrors [ListPatternElemUnficationError]
--
--        unfiyWithNode (tList t1)
--        pure ps
--
--    PRecord t row -> inferPatternNode recordPat $ do
--        fs <- traverse patternNode row
--        unfiyWithNode (tRecord (rowToType (typeOf <$> fs)))
--        pure fs

patternNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
  -> WriterT Node m (ProgPattern (TypeInfo [Error]))
patternNode pat = do
    (p, vs) <- lift pat
    insertPredicates (patternPredicates p)
    tellVars vs
    pure p

exprNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m (ProgExpr (TypeInfo [Error]))
exprNode expr = do
    e <- lift expr
    insertPredicates (exprPredicates e)
    pure e

thisNodeType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => WriterT Node m Type
thisNodeType = do
    t <- newTVar 
    unfiyWithNode t
    pure t

opType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => (TypeInfo [Error] -> a)
  -> Scheme
  -> WriterT Node m a
opType op scheme = do
    (t, (_, _, ps, es)) <- listen (instantiate scheme)
    pure (op (TypeInfo t ps es))

inferOp1Type
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Op1 t
  -> WriterT Node m (Op1 (TypeInfo [Error]))
inferOp1Type = \case
    ONeg _ -> opType ONeg (Forall [kTyp] [InClass "Num" 0] (tGen 0 `fn` tGen 0))
    ONot _ -> opType ONot (Forall [] [] (tBool `fn` tBool))

inferOp2Type
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Op2 t
  -> WriterT Node m (Op2 (TypeInfo [Error]))
inferOp2Type = \case
    OEq  _ -> opType OEq  (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `fn` tGen 0 `fn` tBool))
    ONeq _ -> opType ONeq (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `fn` tGen 0 `fn` tBool))
    OAdd _ -> opType OAdd (Forall [kTyp] [InClass "Num" 0] (tGen 0 `fn` tGen 0 `fn` tGen 0))
    OMul _ -> opType OMul (Forall [kTyp] [InClass "Num" 0] (tGen 0 `fn` tGen 0 `fn` tGen 0))
    OSub _ -> opType OSub (Forall [kTyp] [InClass "Num" 0] (tGen 0 `fn` tGen 0 `fn` tGen 0))
    OAnd _ -> opType OAnd (Forall [] [] (tBool `fn` tBool `fn` tBool))
    OOr  _ -> opType OOr  (Forall [] [] (tBool `fn` tBool `fn` tBool))
    OLt  _ -> opType OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `fn` tGen 0 `fn` tBool))
    OGt  _ -> opType OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `fn` tGen 0 `fn` tBool))
    OLte _ -> opType OLte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `fn` tGen 0 `fn` tBool))
    OGte _ -> opType OGte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `fn` tGen 0 `fn` tBool))

inferClauseType
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => [Type]
  -> Clause t (ProgPattern t) (m (ProgExpr (TypeInfo [Error])))
  -> m (ProgClause (TypeInfo [Error]))
inferClauseType tys eq@(Clause _ pats _) = inferExprNode (args2 Clause) $ do
    (ps, (_, vs, _, _)) <- listen (traverse (patternNode . inferPatternType) pats)
    let schemes = toScheme <$$> vs
        Clause _ _ guards = local (onTypeEnv (Env.inserts schemes)) <$> eq
        (iffs, es) = unzip (guardToPair <$> guards)
    -- Conditions must be Bool
    forM_ (concat iffs) unifyIffCondition
    gs <- traverse inferGuard guards
    pure (ps, gs)

inferGuard
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Guard (m (ProgExpr (TypeInfo [Error])))
  -> WriterT Node m (Guard (ProgExpr (TypeInfo [Error])))
inferGuard (Guard es e) = Guard <$> traverse exprNode es <*> exprNode e

unifyIffCondition
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m ()
unifyIffCondition expr = do
    e <- lift expr
    (_, node) <- listen (e ## (tBool :: Type))
    when (nodeHasErrors node) $
        insertErrors [GuardConditionNotABool]

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

newTVar :: (MonadSupply Name m) => m (TypeT a)
newTVar = do
    k <- ("k" <>) <$> supply
    t <- ("a" <>) <$> supply
    pure (tVar (kVar k) t)

newTVars :: (MonadSupply Name m) => Int -> m [TypeT a]
newTVars = flip replicateM newTVar

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
            , fromPolyType ts <$> (tGen <$> p) )
    modify (third3 (`insertAll` pairs))
    insertPredicates ps
    pure (fromPolyType ts ty)

generalize
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> m Scheme
generalize ty = do
    env <- askTypeEnv
    sub <- gets fst3
    let typ = apply sub ty
        frees = fst <$> free (apply sub env)
        (vs, ks) = unzip $ filter ((`notElem` frees) . fst) (typeVars typ)
        inxd = Map.fromList (zip vs [0..])
    ps <- lookupPredicates vs
    pure (Forall ks (toPred inxd <$> ps) (apply (Sub (tGen <$> inxd)) (toPolyType typ)))
  where
    toPred map (var, tc) = InClass tc (fromJust (Map.lookup var map))

insertAll :: Context -> [(Name, Set Name)] -> Context
insertAll = foldr (uncurry (Env.insertWith Set.union))

lookupConstructor
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> WriterT Node m (Maybe (Set Name, Int))
lookupConstructor con = do
    env <- asks getConstructorEnv
    let info = Env.lookup con env
    when (isNothing info) (insertErrors [MissingDataConstructor con])
    pure info

lookupScheme
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> WriterT Node m Scheme
lookupScheme name = do
    env <- asks getTypeEnv
    sub <- gets fst3
    case Env.lookup name env of
        Nothing -> do
            insertErrors [UnboundTypeIdentifier name]
            toScheme <$> newTVar 
        Just ty ->
            pure (apply sub ty)

lookupPredicates
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => [Name]
  -> m [(Name, Name)]
lookupPredicates vars = do
    env <- gets thd3
    pure [(v, tc) | v <- vars, tc <- Set.toList (Env.findWithDefault mempty v env)]

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

lookupClassInstance
  :: ( MonadState (Substitution Type, Substitution Kind, Context) m
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
        case matchTypes (predicateType classSignature) ty of
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
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => (TypeInfo [Error] -> t -> a)
  -> WriterT Node m t
  -> m (a, [(Name, Type)])
inferPatternNode c f = do
    newTy <- newTVar 
    (a, ti, vs) <- inferNodeType newTy f
    pure (c ti a, vs)

inferExprNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => (TypeInfo [Error] -> t1 -> a)
  -> WriterT Node m t1
  -> m a
inferExprNode c f = do
    newTy <- newTVar 
    (a, ti, _) <- inferNodeType newTy f
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

instance Substitutable (ClassInfo Type (Ast (TypeInfo e))) Type where
    apply sub ClassInfo{..} =
        ClassInfo{ classSuper     = apply sub classSuper
                 , classSignature = apply sub classSignature
                 , .. }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

getClassEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ClassEnv
getClassEnv (e, _, _, _) = e

askClassEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ClassEnv
askClassEnv = asks getClassEnv

getTypeEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> TypeEnv
getTypeEnv (_, e, _, _) = e

askTypeEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m TypeEnv
askTypeEnv = asks getTypeEnv

getKindEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> KindEnv
getKindEnv (_, _, e, _) = e

askKindEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m KindEnv
askKindEnv = asks getKindEnv

getConstructorEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ConstructorEnv
getConstructorEnv (_, _, _, e) = e

askConstructorEnv 
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ConstructorEnv
askConstructorEnv = asks getConstructorEnv

onClassEnv 
  :: (ClassEnv -> ClassEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
onClassEnv f (e1, e2, e3, e4) = (f e1, e2, e3, e4)

onTypeEnv 
  :: (TypeEnv -> TypeEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
onTypeEnv f (e1, e2, e3, e4) = (e1, f e2, e3, e4)

onKindEnv 
  :: (KindEnv -> KindEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
onKindEnv f (e1, e2, e3, e4) = (e1, e2, f e3, e4)

onConstructorEnv 
  :: (ConstructorEnv -> ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) 
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
onConstructorEnv f (e1, e2, e3, e4) = (e1, e2, e3, f e4)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

type Node = 
    ( List Type           -- Types that unify with the node's type
    , List (Name, Type)   -- Pattern variables
    , List Predicate      -- Class predicates
    , List Error          -- Errors
    )

unfiyWithNode :: (MonadWriter Node m) => Type -> m ()
unfiyWithNode ty = tell ([ty], mempty, mempty, mempty)

tellVars :: (MonadWriter Node m) => [(Name, Type)] -> m ()
tellVars vs = tell (mempty, vs, mempty, mempty)

insertPredicates :: (MonadWriter Node m) => [Predicate] -> m ()
insertPredicates ps = tell (mempty, mempty, ps, mempty)

insertErrors :: (MonadWriter Node m) => [Error] -> m ()
insertErrors es = tell (mempty, mempty, mempty, es)

nodeHasErrors :: Node -> Bool
nodeHasErrors (_, _, _, es) = not (Prelude.null es)

nodeVars :: Node -> [(Name, Type)]
nodeVars (_, vs, _, _) = vs

inferNodeType
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> WriterT Node m a
  -> m (a, TypeInfo [Error], [(Name, Type)])
inferNodeType t w = do
    (a, (ts, vs, ps, err)) <- runWriterT w
    errs <- lefts <$> mapM (runUnify t) ts
    sub <- gets fst3
    pure (a, TypeInfo t (nub (apply sub ps)) (err <> errs), vs)

runUnify
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m
     , Typed a
     , Typed b )
  => a
  -> b
  -> m (Either Error ())
runUnify = runExceptT <$$> unifyTyped
  where
    unifyTyped a b = do
        sub <- applyAnd unifyTypes CannotUnify fst3 (typeOf a) (typeOf b)
        modify (first3 (sub <>))
        forM_ (Map.toList (getSub sub)) (uncurry propagate)
      where
        propagate tv ty = do
            env <- gets thd3
            propagateClasses ty (fromMaybe mempty (Env.lookup tv env))

applyAnd
  :: ( MonadState (Substitution Type, Substitution Kind, Context) m
     , Substitutable t1 a, Substitutable t2 a
     , MonadError e m) 
  => (t1 -> t2 -> Except t3 sub)
  -> (t1 -> t2 -> t3 -> e)
  -> ((Substitution Type, Substitution Kind, Context) -> Substitution a)
  -> t1
  -> t2
  -> m sub
applyAnd unify toError sub a b = do
    sub1 <- gets sub
    case runExcept (unify (apply sub1 a) (apply sub1 b)) of
        Left err  -> throwError (toError a b err)
        Right sub -> pure sub

--unifiedT
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Substitution Kind, Context) m
--     , MonadError Error m )
--  => Type
--  -> Type
--  -> m (Substitution Type)
--unifiedT =  

unifiedK k1 = applyAnd unifyKinds KindMismatch snd3 k1 

--unifiedT
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Substitution Kind, Context) m
--     , MonadError Error m )
--  => Type
--  -> Type
--  -> m (Substitution Type)
--unifiedT t1 t2 = do
--    sub1 <- gets fst3
--    case runExcept (unifyTypes (apply sub1 t1) (apply sub1 t2)) of
--        Left err  -> throwError (CannotUnify t1 t2 err)
--        Right sub -> pure sub

--unifiedTK
--  :: ( MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
--     , MonadState (Substitution Type, Substitution Kind, Context) m
--     , MonadError Error m )
--  => Kind
--  -> Kind
--  -> m (Substitution Kind)
--unifiedTK k1 k2 = do
--    sub1 <- gets snd3
--    case runExcept (unifyKinds (apply sub1 k1) (apply sub1 k2)) of
--        Left err  -> throwError (KindMismatch k1 k2 err)
--        Right sub -> pure sub

unifyWith
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m
     , Typed a
     , Typed b
     , Substitutable a Type
     , Substitutable b Type )
  => a
  -> b
  -> WriterT Node m ()
unifyWith a b = do
    traceShowM ">>"
    traceShowM (kindOf (typeOf a))
    traceShowM (kindOf (typeOf b))
    sub <- gets fst3
    runUnify (apply sub a) (apply sub b) 
        >>= whenLeft (insertErrors . pure)

(##)
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m
     , Typed a
     , Typed b
     , Substitutable a Type
     , Substitutable b Type )
  => a
  -> b
  -> WriterT Node m ()
(##) = unifyWith

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Monad transformer stack

type InferState   = StateT (Substitution Type, Substitution Kind, Context)
type InferReader  = ReaderT (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
type InferSupply  = SupplyT Name
type InferStack a = InferReader (InferState (InferSupply a))

runInferState :: (Monad m) => Context -> InferState m a -> m (a, (Substitution Type, Substitution Kind, Context))
runInferState context = flip runStateT (mempty, mempty, context)

runInferReader :: (Monad m) => ClassEnv -> TypeEnv -> KindEnv -> ConstructorEnv -> InferReader m r -> m r
runInferReader e1 e2 e3 e4 = flip runReaderT (e1, e2, e3, e4)

runInferSupply :: (Monad m) => InferSupply m a -> m a
runInferSupply = flip evalSupplyT (numSupply "")

runInfer
  :: (Monad m)
  => Context
  -> ClassEnv
  -> TypeEnv
  -> KindEnv
  -> ConstructorEnv
  -> InferStack m a
  -> m (a, Substitution Type, Substitution Kind, Context)
runInfer context classEnv typeEnv kindEnv constructorEnv =
    runInferReader classEnv typeEnv kindEnv constructorEnv
    >>> runInferState context
    >>> runInferSupply
    >>> fmap to
