{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
module Stuff where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
#if MIN_VERSION_transformers(0,6,0)
import Control.Monad.Trans.Maybe (MaybeT, hoistMaybe)
#else
import Control.Monad.Trans.Maybe (MaybeT(..))
#endif
import Control.Monad.Supply
import Data.Aeson
import Data.Either.Extra (eitherToMaybe)
import Data.Aeson.Encode.Pretty
import Data.Fix (Fix(..))
import Data.Function ((&))
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.List.Extra (notNull)
import Data.Maybe (fromMaybe, fromJust)
import Data.Set.Monad (Set)
import Data.Tuple.Extra
import Data.Void
import Tau.Misc
import Tau.Prettyprinters
import Tau.Serializers
import Tau.Util
import TextShow
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

--

freshType :: (MonadSupply Int m) => m Type
freshType = do
    s <- supply
    let st = showt s
    pure (tVar (kVar ("$k" <> st)) ("$a" <> st))

runTagTree :: ProgExpr t u -> ProgExpr Type u
runTagTree expr = runSupplyNats (tagTree expr)

tagTree :: (MonadSupply Int m) => ProgExpr t u -> m (ProgExpr Type u)
tagTree = cata alg
  where
    alg = \case
        EVar   _ var            -> varExpr   <$> freshType <*> pure var
        ECon   _ con es         -> conExpr   <$> freshType <*> pure con <*> sequence es
        ELit   _ prim           -> litExpr   <$> freshType <*> pure prim
        EApp   _ es             -> appExpr   <$> freshType <*> sequence es
        EFix   _ name e1 e2     -> fixExpr   <$> freshType <*> pure name <*> e1 <*> e2
        ELam   _ ps e           -> lamExpr   <$> freshType <*> traverse tagPattern ps <*> e
        EIf    _ e1 e2 e3       -> ifExpr    <$> freshType <*> e1 <*> e2 <*> e3
        EPat   _ e cs           -> patExpr   <$> freshType <*> e <*> traverse tagClause1 cs
        ELet   _ bind e1 e2     -> letExpr   <$> freshType <*> tagBinding bind <*> e1 <*> e2
        EFun   _ cs             -> funExpr   <$> freshType <*> traverse tagClause cs
        EOp1   _ op a           -> op1Expr   <$> freshType <*> tagOp1 op <*> a
        EOp2   _ op a b         -> op2Expr   <$> freshType <*> tagOp2 op <*> a <*> b
        ETuple _ es             -> tupleExpr <$> freshType <*> sequence es
        EList  _ es             -> listExpr  <$> freshType <*> sequence es
        ERow   _ lab e r        -> rowExpr   <$> freshType <*> pure lab <*> e <*> r
        EHole  _                -> holeExpr  <$> freshType
        EAnn   t a              -> annExpr t <$> a

    tagPattern = cata $ \case
        PVar   _ var            -> varPat    <$> freshType <*> pure var
        PCon   _ name ps        -> conPat    <$> freshType <*> pure name <*> sequence ps
        PAs    _ name p         -> asPat     <$> freshType <*> pure name <*> p
        PLit   _ prim           -> litPat    <$> freshType <*> pure prim
        PAny   _                -> anyPat    <$> freshType
        POr    _ p q            -> orPat     <$> freshType <*> p <*> q
        PTuple _ ps             -> tuplePat  <$> freshType <*> sequence ps
        PList  _ ps             -> listPat   <$> freshType <*> sequence ps
        PRow   _ lab p r        -> rowPat    <$> freshType <*> pure lab <*> p <*> r
        PAnn   t p              -> annPat  t <$> p

    tagBinding = \case
        BPat _ p                -> BPat   <$> freshType <*> tagPattern p
        BFun _ name ps          -> BFun   <$> freshType <*> pure name <*> traverse tagPattern ps

    tagClause = \case
        Clause _ ps choices     -> Clause <$> freshType
                                          <*> traverse tagPattern ps
                                          <*> traverse sequence choices
    tagClause1 = \case
        Clause _ p choices      -> Clause <$> freshType
                                          <*> tagPattern p
                                          <*> traverse sequence choices
    tagOp1 = \case
        ONeg   _                -> ONeg   <$> freshType
        ONot   _                -> ONot   <$> freshType

    tagOp2 = \case
        OEq    _                -> OEq    <$> freshType
        ONeq   _                -> ONeq   <$> freshType
        OAnd   _                -> OAnd   <$> freshType
        OOr    _                -> OOr    <$> freshType
        OAdd   _                -> OAdd   <$> freshType
        OSub   _                -> OSub   <$> freshType
        OMul   _                -> OMul   <$> freshType
        ODiv   _                -> ODiv   <$> freshType
        OPow   _                -> OPow   <$> freshType
        OMod   _                -> OMod   <$> freshType
        OLt    _                -> OLt    <$> freshType
        OGt    _                -> OGt    <$> freshType
        OLte   _                -> OLte   <$> freshType
        OGte   _                -> OGte   <$> freshType
        OLarr  _                -> OLarr  <$> freshType
        ORarr  _                -> ORarr  <$> freshType
        OFpip  _                -> OFpip  <$> freshType
        OBpip  _                -> OBpip  <$> freshType
        OOpt   _                -> OOpt   <$> freshType
        OStr   _                -> OStr   <$> freshType
        ODot   _                -> ODot   <$> freshType
        OField _                -> OField <$> freshType

-------------------------------------------------------------------------------

freshType_ :: (MonadSupply Int m) => m Type
freshType_ = do
    s <- supply
    let st = showt s
    pure (tVar (kVar ("$n" <> st)) ("$v" <> st))

inferAstType
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Ast t Type
  -> m (Ast (TypeInfo [Error]) Void)
inferAstType (Ast expr) =
    Ast <$> (tagTree expr >>= inferExprType >>= applySubsTo)

inferExprType
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgExpr Type Type
  -> m (ProgExpr (TypeInfo [Error]) Void)
inferExprType = cata $ \case

    EVar t var -> do
        lookupScheme var >>= \case
            Nothing ->
                pure (varExpr (TypeInfo [NotInScope var] t []) var)

            Just scheme -> do
                (ty, ps) <- instantiate scheme
                errs <- tryUnify t ty
                pure (varExpr (TypeInfo errs t ps) var)

            -- TODO -- record types

    ECon t con exprs -> do
        es <- sequence exprs
        lookupScheme con >>= \case
            Nothing ->
                pure (conExpr (TypeInfo [ConstructorNotInScope con] t []) con es)

            Just scheme -> do
                (ty, ps) <- instantiate scheme
                errs <- tryUnify ty (foldr tArr t (typeOf <$> es))
                pure (conExpr (TypeInfo errs t ps) con es)

    ELit t prim -> do
        (ty, ps) <- instantiate (inferPrimType prim)
        errs <- tryUnify t ty
        pure (litExpr (TypeInfo errs t ps) prim)

    EApp t exprs -> do
        es <- sequence exprs
        case es of
            [] ->
                error "Implementation error"

            f:args -> do
                ty <- freshType_
                errs1 <- tryUnify t (foldr tArr ty (typeOf <$> filter isHole args))
                errs2 <- tryUnify (typeOf f) (foldr tArr ty (typeOf <$> args))
                pure (appExpr (TypeInfo (errs1 <> errs2) t []) es)

    EFix t name expr1 expr2 -> do
        t1 <- freshType_
        e1 <- local (inTypeEnv (Env.insert name (toScheme t1))) expr1
        errs1 <- tryUnify t t1
        scheme <- generalize (typeOf e1)
        e2 <- local (inTypeEnv (Env.insert name scheme)) expr2
        errs2 <- tryUnify t (typeOf e2)
        pure (fixExpr (TypeInfo (errs1 <> errs2) t []) name e1 e2)

    ELam t pats expr -> do
        (ps, vss) <- unzip <$> traverse inferPatternType pats
        e1 <- local (inTypeEnv (Env.inserts (toScheme <$$> concat vss))) expr
        errs <- tryUnify t (foldr tArr (typeOf e1) (typeOf <$> ps))
        pure (lamExpr (TypeInfo errs t []) ps e1)

    EIf t expr1 expr2 expr3 -> do
        e1 <- expr1
        e2 <- expr2
        e3 <- expr3
        errs1 <- tryUnify (typeOf e1) tBool
        errs2 <- tryUnify (typeOf e2) (typeOf e3)
        errs3 <- tryUnify t (typeOf e2)
        pure (ifExpr (TypeInfo (errs1 <> errs2 <> errs3) t []) e1 e2 e3)

    EPat t expr clauses -> do
        e1 <- expr
        cs <- traverse inferClauseType1 clauses
        undefined

    ELet t (BPat bt pat) expr1 expr2 -> do
        (p, vs) <- inferPatternType pat
        e1 <- expr1
        errs1 <- tryUnify (typeOf p) (typeOf e1)
        schemes <- traverse (secondM generalize) vs
        e2 <- local (inTypeEnv (Env.inserts schemes)) expr2
        errs2 <- tryUnify t (typeOf e2)
        undefined

    ELet t (BFun bt f pats) expr1 expr2 -> do
        (ps, vss) <- unzip <$> traverse inferPatternType pats
        e1 <- local (inTypeEnv (Env.inserts (toScheme <$$> concat vss))) expr1
        t1 <- freshType_
        errs1 <- tryUnify t1 (foldr tArr (typeOf e1) (typeOf <$> ps))
        scheme <- generalize t1
        e2 <- local (inTypeEnv (Env.insert f scheme)) expr2
        errs2 <- tryUnify t (typeOf e2)
        undefined

    EFun t clauses -> do
        cs <- traverse inferClauseType clauses
        errss <- forM cs $ \(Clause ti ps gs) -> do
            concat <$> forM gs (\(Choice _ e) -> do
                errs1 <- tryUnify t (foldr tArr (typeOf e) (typeOf <$> ps))
                errs2 <- tryUnify (typeOf ti) (typeOf e)
                pure (errs1 <> errs2))
        pure (funExpr (TypeInfo (concat errss) t []) cs)

    EOp1 t op1 expr -> do
        a <- expr
        (op, ps) <- inferOp1Type op1
        errs <- tryUnify (typeOf op) (typeOf a `tArr` t)
        pure (op1Expr (TypeInfo errs t ps) op a)

    EOp2 t op2 expr1 expr2 -> do
        a <- expr1
        b <- expr2
        (op, ps) <- inferOp2Type op2
        ty <- freshType_
        errs1 <- tryUnify t (foldr tArr ty (typeOf <$> filter isHole [a, b]))
        errs2 <- tryUnify (typeOf op) (foldr tArr ty (typeOf <$> [a, b]))
        pure (op2Expr (TypeInfo (errs1 <> errs2) t ps) op a b)

    ETuple t exprs -> do
        es <- sequence exprs
        errs <- tryUnify t (tTuple (typeOf <$> es))
        pure (tupleExpr (TypeInfo errs t []) es)

    EList t exprs -> do
        es <- sequence exprs
        t1 <- case es of
            []    -> freshType_
            (e:_) -> pure (typeOf e)

        errss <- forM es (tryUnify t1 . typeOf)
        errs1 <- tryUnify t (tList t1)
        pure (listExpr (TypeInfo (errs1 <> concat errss) t []) es)

    ERow t label expr row -> do
        e <- expr
        r <- row
        errs <- tryUnify t (tRow label (typeOf e) (typeOf r))
        pure (rowExpr (TypeInfo errs t []) label e r)

    EHole t ->
        pure (holeExpr (TypeInfo [] t []))

    EAnn t expr -> do
        e <- expr
        let TypeInfo errs1 t1 ps = exprTag e
        errs2 <- tryUnify t t1
        pure (setExprTag (TypeInfo (errs1 <> errs2) t1 ps) e)

inferPatternType
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgPattern Type Type
  -> m (ProgPattern (TypeInfo [Error]) Void, [(Name, Type)])
inferPatternType = cata $ \case

    PVar t var ->
        pure (varPat (TypeInfo [] t []) var, [(var, t)])

    PCon t con pats -> do
        (ps, vss) <- unzip <$> sequence pats
        matchConstructor con (length ps) >>= \case
            Left errs ->
                pure (conPat (TypeInfo errs t []) con ps, [])

            Right scheme -> do
                (ty, qs) <- instantiate scheme
                errs <- tryUnify ty (foldr tArr t (typeOf <$> ps))
                pure (conPat (TypeInfo errs t qs) con ps, concat vss)

    PAs t name pat -> do
        (p, vs) <- pat
        errs <- tryUnify t (typeOf p)
        pure (asPat (TypeInfo errs t []) name p, vs)

    PLit t prim -> do
        (ty, ps) <- instantiate (inferPrimType prim)
        errs <- tryUnify t ty
        pure (litPat (TypeInfo errs t ps) prim, [])

    PAny t ->
        pure (anyPat (TypeInfo [] t []), [])

    POr t pat1 pat2 -> do
        (p1, vs1) <- pat1
        (p2, vs2) <- pat2
        errs1 <- tryUnify t (typeOf p1)
        errs2 <- tryUnify t (typeOf p2)
        pure (orPat (TypeInfo (errs1 <> errs2) t []) p1 p2, vs1 <> vs2)

    PTuple t pats -> do
        (ps, vss) <- unzip <$> sequence pats
        errs <- tryUnify t (tTuple (typeOf <$> ps))
        pure (tuplePat (TypeInfo errs t []) ps, concat vss)

    PList t pats -> do
        (ps, vss) <- unzip <$> sequence pats
        t1 <- case ps of
            []    -> freshType_
            (p:_) -> pure (typeOf p)

        errss <- forM ps (tryUnify t1 . typeOf)
        errs1 <- tryUnify t (tList t1)
        pure (listPat (TypeInfo (errs1 <> concat errss) t []) ps, concat vss)

    PRow t label pat row -> do
        p <- pat
        (r, vs) <- row
        undefined

    PAnn t pat -> do
        (p, vs) <- pat
        let TypeInfo errs1 t1 ps = patternTag p
        errs2 <- tryUnify t t1
        pure (setPatternTag (TypeInfo (errs1 <> errs2) t1 ps) p, vs)

inferOp1Type
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Op1 Type
  -> m (Op1 (TypeInfo [Error]), [Predicate])
inferOp1Type = \case

    ONeg   t -> opType t ONeg (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0))
    ONot   t -> opType t ONot (Forall [] [] (tBool `tArr` tBool))

inferOp2Type
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Op2 Type
  -> m (Op2 (TypeInfo [Error]), [Predicate])
inferOp2Type = \case

    OEq    t -> opType t OEq  (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    ONeq   t -> opType t ONeq (Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OAnd   t -> opType t OAnd (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OOr    t -> opType t OOr  (Forall [] [] (tBool `tArr` tBool `tArr` tBool))
    OAdd   t -> opType t OAdd (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OSub   t -> opType t OSub (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    OMul   t -> opType t OMul (Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    ODiv   t -> undefined
    OPow   t -> undefined
    OMod   t -> undefined
    OLt    t -> opType t OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGt    t -> opType t OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLte   t -> opType t OLte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGte   t -> opType t OGte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLarr  t -> undefined
    ORarr  t -> undefined
    OFpip  t -> undefined
    OBpip  t -> undefined
    OOpt   t -> undefined
    OStr   t -> opType t OOpt (Forall [] [] (tString `tArr` tString `tArr` tString))
    ODot   t -> undefined
    OField t -> undefined

opType
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> (TypeInfo [Error] -> a)
  -> Scheme
  -> m (a, [Predicate])
opType t op scheme = do
    (ty, ps) <- instantiate scheme
    errs <- tryUnify t ty
    pure (op (TypeInfo errs ty ps), ps)

inferPrimType :: Prim -> Scheme
inferPrimType = \case
    TUnit      -> Forall [] [] tUnit
    TBool{}    -> Forall [] [] tBool
    TChar{}    -> Forall [] [] tChar
    TString{}  -> Forall [] [] tString
    TInt{}     -> Forall [kTyp] [InClass "Num" 0] (tGen 0)
    TInteger{} -> Forall [kTyp] [InClass "Num" 0] (tGen 0)
    TFloat{}   -> Forall [kTyp] [InClass "Fractional" 0] (tGen 0)
    TDouble{}  -> Forall [kTyp] [InClass "Fractional" 0] (tGen 0)
    TSymbol{}  -> Forall [kTyp] [] (tGen 0)

inferClauseType
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Clause t [ProgPattern Type Type] (m (ProgExpr (TypeInfo [Error]) Void))
  -> m (Clause (TypeInfoT [Error] t) [ProgPattern (TypeInfo [Error]) Void] (ProgExpr (TypeInfo [Error]) Void))
inferClauseType clause =
    traverse inferPatternType (clausePatterns clause)
        >>= unifyClause clause . second concat . unzip

inferClauseType1
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Clause t (ProgPattern Type Type) (m (ProgExpr (TypeInfo [Error]) Void))
  -> m (Clause (TypeInfoT [Error] t) (ProgPattern (TypeInfo [Error]) Void) (ProgExpr (TypeInfo [Error]) Void))
inferClauseType1 clause =
    inferPatternType (clausePatterns clause)
        >>= unifyClause clause

unifyClause
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Clause t p1 (m (ProgExpr (TypeInfo [Error]) Data.Void.Void))
  -> (p2, [(Name, Type)])
  -> m (Clause (TypeInfoT [Error] t) p2 (ProgExpr (TypeInfo [Error]) Data.Void.Void))
unifyClause eq@(Clause t _ _) (ps, vs) = do
    let schemes = toScheme <$$> vs
        Clause _ _ choices = local (inTypeEnv (Env.inserts schemes)) <$> eq
        (whens, _) = unzip (choiceToPair <$> choices)
    errss <- forM (concat whens) unifyWhen
    gs <- traverse inferChoice choices
    pure (Clause (TypeInfo (concat errss) t []) ps gs)

choiceToPair :: Choice a -> ([a], a)
choiceToPair (Choice es e) = (es, e)
{-# INLINE choiceToPair #-}

unifyWhen
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => m (ProgExpr (TypeInfo [Error]) Void)
  -> m [Error]
unifyWhen expr = do
    e <- expr
    errs <- tryUnify tBool (typeOf e)
    pure [NonBooleanGuard e | notNull errs]

inferChoice
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Choice (m (ProgExpr (TypeInfo [Error]) Void))
  -> m (Choice (ProgExpr (TypeInfo [Error]) Void))
inferChoice (Choice exprs expr) = Choice <$> sequence exprs <*> expr

#if !MIN_VERSION_transformers(0,6,0)
hoistMaybe :: (Applicative m) => Maybe b -> MaybeT m b
hoistMaybe = MaybeT . pure
#endif

lookupScheme
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> m (Maybe Scheme)
lookupScheme name = runMaybeT $ do
    env <- askTypeEnv
    scheme <- hoistMaybe (Env.lookup name env)
    applySubsTo scheme

lookupPredicates
  :: (MonadState (Substitution Type, Substitution Kind, Context) m)
  => [Name]
  -> m [(Name, Name)]
lookupPredicates vars = do
    env <- gets thd3
    pure $ do
        v  <- vars
        tc <- Set.toList (Env.findWithDefault mempty v env)
        [(v, tc)]

lookupConstructor
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> m (Maybe (Set Name, Int))
lookupConstructor con = Env.lookup con <$> askConstructorEnv

matchConstructor
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> Int
  -> m (Either [Error] Scheme)
matchConstructor con n =
    lookupConstructor con >>= \case
        Nothing ->
            pure (Left [ConstructorNotInScope con])

        Just (_, arity) ->
            if arity /= n
                then pure (Left [PatternArityMismatch con arity n])
                else maybeToEither [ConstructorNotInScope con] <$> lookupScheme con

applySubsTo
  :: ( MonadState (Substitution Type, Substitution Kind, c) m
     , Substitutable t Type
     , Substitutable t Kind )
  => t
  -> m t
applySubsTo t = do
    (typeSub, kindSub, _) <- get
    pure (applyBoth (typeSub, kindSub) t)

instantiate
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Scheme
  -> m (Type, [Predicate])
instantiate (Forall kinds preds ty) = do
    names <- ("$v" <>) . showt <$$> supplies (length kinds)
    let ts = zipWith tVar kinds names
        (pairs, ps) = unzip (fn <$> preds)
        fn p@(InClass tc ix) =
            ( (names !! ix, Set.singleton tc)
            , fromPolytype ts <$> (tGen <$> p) )
    addToContext pairs
    pure (fromPolytype ts ty, ps)

insertAll :: Context -> [(Name, Set Name)] -> Context
insertAll = foldr (uncurry (Env.insertWith Set.union))

addToContext :: (MonadState (a, b, Context) m) => [(Name, Set Name)] -> m ()
addToContext ps = modify (third3 (`insertAll` ps))

tryUnify
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> Type
  -> m [Error]
tryUnify t1 t2 = either pure (const []) <$> runExceptT (do
    a <- applySubsTo t1
    b <- applySubsTo t2
    (typeSub, kindSub) <- withExceptT UnificationError (unifyTypes a b)
    modify (first3 (typeSub <>))
    modify (second3 (kindSub <>))
    forM_ (Map.toList (getSub typeSub)) $ \(tv, ty) -> do
        env <- gets thd3
        propagateClasses ty (fromMaybe mempty (Env.lookup tv env)))

propagateClasses
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadError Error m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> Set Name
  -> m ()
propagateClasses (Fix (TVar _ var)) ps
    | Set.null ps = pure ()
    | otherwise   = modify (third3 (Env.insertWith Set.union var ps))
propagateClasses ty ps =
    forM_ ps $ \name -> do
        ClassInfo{ classPredicates = preds } <- lookupClassInstance name ty
        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]

lookupClassInstance
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadError Error m )
  => Name
  -> Type
  -> m (ClassInfo Type (Ast (TypeInfo ()) Void))
lookupClassInstance name ty = do
    env <- askClassEnv
    (_, insts) <- liftMaybe (NoSuchClass name) (Env.lookup name env)
    info <- sequence [tryMatch i | i <- insts]
    msum info & maybe (throwError (MissingInstance name ty)) pure
  where
    tryMatch info@ClassInfo{..} = do
        sub <- eitherToMaybe <$> runExceptT (matchTypes (predicateType classSignature) ty)
        pure (applyBoth <$> sub <*> pure info)

generalize
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> m Scheme
generalize ty = do
    env <- askTypeEnv
    (sub1, sub2, _) <- get
    let t1 = applyBoth (sub1, sub2) ty
        frees = fst <$> free (applyBoth (sub1, sub2) env)
        (vs, ks) = unzip $ filter ((`notElem` frees) . fst) (typeVars t1)
        ixd = Map.fromList (zip vs [0..])
    ps <- lookupPredicates vs
    pure (Forall ks (toPred ixd <$> ps) (apply (Sub (tGen <$> ixd)) (toPolytype t1)))
  where
    toPred map (var, tc) = InClass tc (fromJust (Map.lookup var map))

-------------------------------------------------------------------------------

getClassEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ClassEnv
getClassEnv (e, _, _, _) = e
{-# INLINE getClassEnv #-}

askClassEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ClassEnv
askClassEnv = asks getClassEnv
{-# INLINE askClassEnv #-}

getTypeEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> TypeEnv
getTypeEnv (_, e, _, _) = e
{-# INLINE getTypeEnv #-}

askTypeEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m TypeEnv
askTypeEnv = asks getTypeEnv
{-# INLINE askTypeEnv #-}

getKindEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> KindEnv
getKindEnv (_, _, e, _) = e
{-# INLINE getKindEnv #-}

askKindEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m KindEnv
askKindEnv = asks getKindEnv
{-# INLINE askKindEnv #-}

getConstructorEnv :: (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) -> ConstructorEnv
getConstructorEnv (_, _, _, e) = e
{-# INLINE getConstructorEnv #-}

askConstructorEnv
  :: MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
  => m ConstructorEnv
askConstructorEnv = asks getConstructorEnv
{-# INLINE askConstructorEnv #-}

inClassEnv
  :: (ClassEnv -> ClassEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inClassEnv f (e1, e2, e3, e4) = (f e1, e2, e3, e4)
{-# INLINE inClassEnv #-}

inTypeEnv
  :: (TypeEnv -> TypeEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inTypeEnv f (e1, e2, e3, e4) = (e1, f e2, e3, e4)
{-# INLINE inTypeEnv #-}

inKindEnv
  :: (KindEnv -> KindEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inKindEnv f (e1, e2, e3, e4) = (e1, e2, f e3, e4)
{-# INLINE inKindEnv #-}

inConstructorEnv
  :: (ConstructorEnv -> ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
  -> (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
inConstructorEnv f (e1, e2, e3, e4) = (e1, e2, e3, f e4)
{-# INLINE inConstructorEnv #-}

-------------------------------------------------------------------------------

type InferState  = StateT (Substitution Type, Substitution Kind, Context)
type InferReader = ReaderT (ClassEnv, TypeEnv, KindEnv, ConstructorEnv)
type InferSupply = SupplyT Int
type InferStack a = InferReader (InferState (InferSupply (MaybeT a)))

runInferState :: (Monad m) => Context -> InferState m a -> m (a, (Substitution Type, Substitution Kind, Context))
runInferState context = flip runStateT (mempty, mempty, context)

runInferReader :: (Monad m) => ClassEnv -> TypeEnv -> KindEnv -> ConstructorEnv -> InferReader m r -> m r
runInferReader e1 e2 e3 e4 = flip runReaderT (e1, e2, e3, e4)

runInferT
  :: (Monad m)
  => Context
  -> ClassEnv
  -> TypeEnv
  -> KindEnv
  -> ConstructorEnv
  -> InferStack m a
  -> m (a, (Substitution Type, Substitution Kind, Context))
runInferT context classEnv typeEnv kindEnv constructorEnv =
    runInferReader classEnv typeEnv kindEnv constructorEnv
        >>> runInferState context
        >>> runSupplyNatsT

runInfer
  :: Context
  -> ClassEnv
  -> TypeEnv
  -> KindEnv
  -> ConstructorEnv
  -> InferStack Identity a
  -> (a, (Substitution Type, Substitution Kind, Context))
runInfer context classEnv typeEnv kindEnv constructorEnv =
    runIdentity . runInferT context classEnv typeEnv kindEnv constructorEnv

-------------------------------------------------------------------------------

isHole
  :: (Functor e2, Functor e4)
  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Bool
isHole = project >>> \case
    EHole{} -> True
    _       -> False

-------------------------------------------------------------------------------

test1 =
    runSupplyNats (tagTree tree)
  where
    tree =
        appExpr ()
            [ op2Expr () (OAdd ()) (holeExpr ()) (holeExpr ())
            , annExpr tInt (litExpr () (TInteger 5))
            , annExpr tInt (litExpr () (TInteger 5))
            ]

-------------------------------------------------------------------------------

test2 = runSupplyNats subs
  where
    subs = unifyTypes2
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
        (tRow "shoeSize" tFloat (tVar kRow "r"))
    unifyTypes2 a b = do
        runExceptT (unifyTypes a b) -- (+1) (0 :: Int)

--instance MonadError (Either UnificationError a) where
--
----unifyTypes2
----  :: ( MonadSupply Int y z
----     , MonadError UnificationError m )
----  => Type
----  -> Type
----  -> m (Substitution Type, Substitution Kind)
----unifyTypes2 :: Type -> Type -> SupplyT s0 (Either UnificationError) (Substitution Type, Substitution Kind)
--unifyTypes2 :: Type -> Type -> Either UnificationError (Substitution Type, Substitution Kind)

-------------------------------------------------------------------------------

test3 :: ProgExpr t Type -> (ProgExpr (TypeInfo [Error]) Void, (Substitution Type, Substitution Kind, Context))
test3 expr =
    runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (tagTree expr >>= inferExprType)

test4 = test3 (varExpr () "xxx")

test5expr :: ProgExpr () Type
test5expr = funExpr () [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "[]" []] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] [Choice [] (litExpr () (TBool True))] ]

test5 :: IO ()
test5 = liftIO $ LBS.writeFile "/home/laserpants/code/tau-tooling/src/tmp/bundle.json" (encodePretty' defConfig{ confIndent = Spaces 2 } (toRep bundle))
    -- astExpr a
  where
    ast = Ast test5expr
    (a, _) = runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType ast)

    bundle = Bundle
        { sourceExpr = test5expr
        , typedExpr  = astExpr a
        }


data Bundle = Bundle
    { sourceExpr  :: ProgExpr () Type
    , typedExpr   :: ProgExpr (TypeInfo [Error]) Void
    } deriving (Show, Eq)

instance ToRep Bundle where
    toRep Bundle{..} =
        object
            [ "source"  .= toRep sourceExpr
            , "typed"   .= toRep typedExpr
            ]

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

testKindEnv :: KindEnv
testKindEnv = Env.fromList
    [ ( "Num" , kArr kTyp kClass )
    ]

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Zero"         , Forall []     [] (tCon kTyp "Nat") )
    , ( "Succ"         , Forall []     [] (tCon kTyp "Nat" `tArr` tCon kTyp "Nat") )
    , ( "Leaf"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Tree") (tGen 0)) )
    , ( "Node"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0)) )
    , ( "Leaf'"        , Forall [kTyp, kTyp] [] (tApp kTyp (tApp kFun (tCon kFun2 "Tree'") (tGen 0)) (tGen 1)) )
    , ( "Node'"        , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tGen 1 `tArr` tGen 1 `tArr` tApp kTyp (tApp kFun (tCon kFun2 "Tree'") (tGen 0)) (tGen 1)) )
    , ( "Nil'"         , Forall [kTyp, kTyp] [] (tApp kTyp (tApp kFun (tCon kFun2 "List'") (tGen 0)) (tGen 1)) )
    , ( "Cons'"        , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tGen 1 `tArr` tApp kTyp (tApp kFun (tCon kFun2 "List'") (tGen 0)) (tGen 1)) )
    , ( "Foo"          , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
    , ( "id"           , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
    , ( "(::)"         , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "(==)"         , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool) )
    , ( "testFun1"     , Forall [kTyp] [InClass "Num" 0, InClass "Eq" 0] (tGen 0 `tArr` tBool) )
    , ( "length"       , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )
    , ( "[]"           , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "(+)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "#"            , Forall [kRow] [] (tGen 0 `tArr` tApp kTyp tRecordCon (tGen 0)) )
    , ( "{}"           , Forall [] [] tRowNil )
    , ( "_#"           , Forall [kRow] [] (tApp kTyp (tCon (kArr kRow kTyp) "#") (tGen 0) `tArr` tGen 0) )
    , ( "fromInteger"  , Forall [kTyp] [InClass "Num" 0] (tInteger `tArr` tGen 0) )
    , ( "fn1"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))
    ]

testClassEnv :: ClassEnv
testClassEnv = Env.fromList
    [ ( "Show"
        -- Interface
      , ( ClassInfo (InClass "Show" "a") []
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) []
              [ ( "show", Ast (varExpr (TypeInfo () (tInt `tArr` tString) []) "@Int.Show") )
              ]
          , ClassInfo (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b"))) []
              [ ( "show", Ast (varExpr (TypeInfo () (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "TODO") )
              ]
          ]
        )
      )
    , ( "Ord"
        -- Interface
      , ( ClassInfo (InClass "Ord" "a") []
            [ ( "(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            , ( "(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            , ( "(>=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            , ( "(<=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            ]
        -- Instances
        , [ ClassInfo (InClass "Ord" tInt) []
              [ ( "(>)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)") )
              , ( "(<)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<)") )
              , ( "(>=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>=)") )
              , ( "(<=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<=)") )
              ]
          ]
        )
      )
    , ( "Eq"
        -- Interface
      , ( ClassInfo (InClass "Eq" "a") [] -- [InClass "Ord" "a"]
            [ ( "(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            , ( "(/=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            ]
        -- Instances
        , [ ClassInfo (InClass "Eq" tInt) []
            [ ( "(==)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(/=)" ) )
            ]
          , ClassInfo (InClass "Eq" tInteger) []
            [ ( "(==)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Integer.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Integer.(/=)" ) )
            ]
          , ClassInfo (InClass "Eq" tBool) []
            [ ( "(==)", Ast (varExpr (TypeInfo () (tBool `tArr` tBool `tArr` tBool) []) "@Bool.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tBool `tArr` tBool `tArr` tBool) []) "@Bool.(/=)" ) )
            ]
          , ClassInfo (InClass "Eq" tString) []
            [ ( "(==)", Ast (varExpr (TypeInfo () (tString `tArr` tString `tArr` tString) []) "@String.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tString `tArr` tString `tArr` tString) []) "@String.(/=)" ) )
            ]
          ]
        )
      )
    , ( "Foo"
        -- Interface
      , ( ClassInfo (InClass "Foo" "a") []
            -- [ ( "foo", tInt )
            [ ( "foo", tBool )
            ]
        -- Instances
        , [ ClassInfo (InClass "Foo" tInt) []
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 5))) )
            [ ( "foo", Ast (litExpr (TypeInfo () tBool []) (TBool True)) ) ]
          , ClassInfo (InClass "Foo" tInteger) []
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 7))) )
            [ ( "foo", Ast (litExpr (TypeInfo () tBool []) (TBool False)) ) ]
          ]
        )
      )
    , ( "Num"
        -- Interface
      , ( ClassInfo (InClass "Num" "a") [InClass "Eq" "a", InClass "Foo" "a"]
            [ ( "(+)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "(*)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "(-)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "fromInteger" , tInteger `tArr` tVar kTyp "a" )
            ]
        -- Instances
        , [ ClassInfo (InClass "Num" tInt) []
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)") )
            , ( "(*)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)") )
            , ( "(-)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInt) []) "@Int.fromInteger") )
            ]
          , ClassInfo (InClass "Num" tInteger) []
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(+)") )
            , ( "(*)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(*)") )
            , ( "(-)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(-)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger) []) "@Integer.id") )
            ]
          ]
        )
      )
    ]

constructorEnv :: [(Name, ([Name], Int))] -> ConstructorEnv
constructorEnv = Env.fromList . (first Set.fromList <$$>)

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ( ["Some", "None"], 1 ))
    , ("None"     , ( ["Some", "None"], 0 ))
    , ("Zero"     , ( ["Zero", "Succ"], 0 ))
    , ("Succ"     , ( ["Zero", "Succ"], 1 ))
    , ("Leaf"     , ( ["Leaf", "Node"], 0 ))
    , ("Node"     , ( ["Leaf", "Node"], 3 ))
    , ("Leaf'"    , ( ["Leaf'", "Node'"], 0 ))
    , ("Node'"    , ( ["Leaf'", "Node'"], 5 ))
    , ("[]"       , ( ["[]", "(::)"], 0 ))
    , ("(::)"     , ( ["[]", "(::)"], 2 ))
    , ("(,)"      , ( ["(,)"], 2 ))
    , ("Foo"      , ( ["Foo"], 2 ))
    , ("#"        , ( ["#"], 1 ))
    , ("{}"       , ( ["{}"], 0 ))
    , ("Cons'"    , ( ["Nil'", "Cons'"], 3 ))
    , ("Nil'"     , ( ["Nil'", "Cons'"], 0 ))
    ]

-- testEvalEnv :: ValueEnv Eval
-- testEvalEnv = Env.fromList
--     [ -- ( "(,)" , constructor "(,)" 2 )
--       ( "_#"  , fromJust (evalExpr (cLam "?0" (cPat (cVar "?0") [(["#", "?1"], cVar "?1")])) mempty) )
--     , ( "(.)" , fromJust (evalExpr (cLam "f" (cLam "x" (cApp [cVar "f", cVar "x"]))) mempty) )
-- --    , ( "fn1" , fromJust (evalExpr (cLam "?0" (cLam "?1" (cApp [cVar "@Integer.(+)", cVar "?0", cVar "?1"]))) mempty) )
--     ]