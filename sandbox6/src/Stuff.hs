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
import Data.Aeson.Encode.Pretty
import Data.Either.Extra (eitherToMaybe)
import Data.Fix (Fix(..))
import Data.Function ((&))
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.List.Extra (notNull)
import Data.Maybe (fromMaybe, fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Tuple.Extra
import Data.Void
import Debug.Trace
import Tau.Eval
import Tau.Misc
import Tau.Parse
import Tau.Prettyprinters
import Tau.Serializers
import Tau.Tree
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
        EVar    _ var           -> varExpr    <$> freshType <*> pure var
        ECon    _ con es        -> conExpr    <$> freshType <*> pure con <*> sequence es
        ELit    _ prim          -> litExpr    <$> freshType <*> pure prim
        EApp    _ es            -> appExpr    <$> freshType <*> sequence es
        EFix    _ name e1 e2    -> fixExpr    <$> freshType <*> pure name <*> e1 <*> e2
        ELam    _ ps e          -> lamExpr    <$> freshType <*> traverse tagPattern ps <*> e
        EIf     _ e1 e2 e3      -> ifExpr     <$> freshType <*> e1 <*> e2 <*> e3
        EPat    _ e cs          -> patExpr    <$> freshType <*> e <*> traverse tagClause1 cs
        ELet    _ bind e1 e2    -> letExpr    <$> freshType <*> tagBinding bind <*> e1 <*> e2
        EFun    _ cs            -> funExpr    <$> freshType <*> traverse tagClause cs
        EOp1    _ op a          -> op1Expr    <$> freshType <*> tagOp1 op <*> a
        EOp2    _ op a b        -> op2Expr    <$> freshType <*> tagOp2 op <*> a <*> b
        ETuple  _ es            -> tupleExpr  <$> freshType <*> sequence es
        EList   _ es            -> listExpr   <$> freshType <*> sequence es
        ERow    _ lab e r       -> rowExpr    <$> freshType <*> pure lab <*> e <*> r
        ERecord _ e             -> recordExpr <$> freshType <*> e
        EHole   _               -> holeExpr   <$> freshType
        EAnn    t a             -> annExpr t  <$> a

    tagPattern = cata $ \case
        PVar    _ var           -> varPat     <$> freshType <*> pure var
        PCon    _ name ps       -> conPat     <$> freshType <*> pure name <*> sequence ps
        PAs     _ name p        -> asPat      <$> freshType <*> pure name <*> p
        PLit    _ prim          -> litPat     <$> freshType <*> pure prim
        PAny    _               -> anyPat     <$> freshType
        POr     _ p q           -> orPat      <$> freshType <*> p <*> q
        PTuple  _ ps            -> tuplePat   <$> freshType <*> sequence ps
        PList   _ ps            -> listPat    <$> freshType <*> sequence ps
        PRow    _ lab p r       -> rowPat     <$> freshType <*> pure lab <*> p <*> r
        PRecord _ p             -> recordPat  <$> freshType <*> p
        PAnn    t p             -> annPat  t  <$> p

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

inferAstType
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgExpr t Type
  -> m (Ast (TypeInfo [Error]))
inferAstType expr =
    Ast <$> (tagTree (preproc expr) >>= inferExprType >>= applySubsTo)
  where
    preproc = cata $ \case
        ERow t label expr row -> rowExpr t label expr next
          where
            next = case project row of
                -- To make the types align, a special deconstructor function
                -- of type { r } -> r is applied to the final row if it is
                -- a variable.
                EVar _ v -> appExpr t [varExpr t "_#", varExpr t v]
                _        -> row

        e -> embed e

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
                -- Special case for record/row types
                lookupScheme ("#" <> var) >>= \case
                    Just scheme -> do
                        (ty, ps) <- instantiate scheme
                        errs <- tryUnify t ty
                        pure (recordExpr (TypeInfo errs (tRecord t) ps) (varExpr (TypeInfo [] t []) var))

                    Nothing ->
                        pure (varExpr (TypeInfo [NotInScope var] t []) var)

            Just scheme -> do
                (ty, ps) <- instantiate scheme
                errs <- tryUnify t ty
                pure (varExpr (TypeInfo errs t ps) var)

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
                ty <- fresh
                errs1 <- tryUnify t (foldr tArr ty (typeOf <$> filter isHole args))
                errs2 <- tryUnify (typeOf f) (foldr tArr ty (typeOf <$> args))
                pure (appExpr (TypeInfo (errs1 <> errs2) t []) es)

    EFix t name expr1 expr2 -> do
        t1 <- fresh
        e1 <- local (inTypeEnv (Env.insert name (toScheme t1))) expr1
        errs1 <- tryUnify (typeOf e1) t1
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
        errss <- forM cs $ \(Clause ti p ds) -> do
            errs1 <- concat <$> forM ds (\(Choice _ e) ->
                tryUnify t (typeOf e))
            errs2 <- tryUnify t (typeOf ti)
            errs3 <- tryUnify (typeOf e1) (typeOf p)
            pure (errs1 <> errs2 <> errs3)
        pure (patExpr (TypeInfo (concat errss) t []) e1 cs)

    ELet t (BPat bt pat) expr1 expr2 -> do
        (p, vs) <- inferPatternType pat
        e1 <- expr1
        errs1 <- tryUnify (typeOf p) (typeOf e1)
        schemes <- traverse (secondM generalize) vs
        e2 <- local (inTypeEnv (Env.inserts schemes)) expr2
        errs2 <- tryUnify t (typeOf e2)
        errs3 <- tryUnify bt (typeOf e1)
        pure (letExpr (TypeInfo (errs1 <> errs2 <> errs3) t []) (BPat (TypeInfo [] bt []) p) e1 e2)

    ELet t (BFun bt f pats) expr1 expr2 -> do
        (ps, vss) <- unzip <$> traverse inferPatternType pats
        e1 <- local (inTypeEnv (Env.inserts (toScheme <$$> concat vss))) expr1
        t1 <- fresh
        errs1 <- tryUnify t1 (foldr tArr (typeOf e1) (typeOf <$> ps))
        scheme <- generalize t1
        e2 <- local (inTypeEnv (Env.insert f scheme)) expr2
        errs2 <- tryUnify t (typeOf e2)
        errs3 <- tryUnify t1 bt
        pure (letExpr (TypeInfo (errs1 <> errs2 <> errs3) t []) (BFun (TypeInfo [] bt []) f ps) e1 e2)

    EFun t clauses -> do
        cs <- traverse inferClauseType clauses
        errss <- forM cs $ \(Clause ti ps ds) -> do
            concat <$> forM ds (\(Choice _ e) -> do
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

        ty <- applySubsTo (typeOf b)
        field <- case (project a, unpackRecordType ty) of
            (EVar _ name, Just row) ->
                (,) name <$$> lookupRowType name <$> applySubsTo row
            _ ->
                pure Nothing

        case (op2, field) of
            (ODot t1, Just (name, t2)) -> do
                (op, ps) <- inferOp2Type (OField t1)
                errs1 <- tryUnify (typeOf op) (typeOf a `tArr` typeOf b `tArr` t)
                errs2 <- tryUnify t t2
                pure (op2Expr (TypeInfo (errs1 <> errs2) t ps) op
                              (litExpr (TypeInfo [] tSymbol []) (TSymbol name)) b)
            _ -> do
                (op, ps) <- inferOp2Type op2
                ty <- fresh
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
            []    -> fresh
            (e:_) -> pure (typeOf e)

        errss <- forM es (tryUnify t1 . typeOf)
        errs1 <- tryUnify t (tList t1)
        pure (listExpr (TypeInfo (errs1 <> concat errss) t []) es)

    ERow t label expr row -> do
        e <- expr
        r <- row
        errs1 <- tryUnify t (tRow label (typeOf e) (typeOf r))
        (ty, _) <- instantiate (Forall [kTyp, kRow] [] (tRow label (tGen 0) (tGen 1)))
        errs2 <- tryUnify t ty
        pure (rowExpr (TypeInfo (errs1 <> errs2) t []) label e r)

    ERecord t expr -> do
        e <- expr
        errs <- tryUnify t (tRecord (typeOf e))
        pure (recordExpr (TypeInfo errs t []) e)

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
            []    -> fresh
            (p:_) -> pure (typeOf p)

        errss <- forM ps (tryUnify t1 . typeOf)
        errs1 <- tryUnify t (tList t1)
        pure (listPat (TypeInfo (errs1 <> concat errss) t []) ps, concat vss)

    PRow t label pat row -> do
        (p, vs1) <- pat
        (r, vs2) <- row
        errs1 <- tryUnify t (tRow label (typeOf p) (typeOf r))
        (ty, _) <- instantiate (Forall [kTyp, kRow] [] (tRow label (tGen 0) (tGen 1)))
        errs2 <- tryUnify t ty
        pure (rowPat (TypeInfo (errs1 <> errs2) t []) label p r, vs1 <> tag vs2 r)
      where
        -- { ... | r }
        tag :: [(Name, Type)] -> ProgPattern (TypeInfo [Error]) Void -> [(Name, Type)]
        tag vs = project >>> \case
              PVar t v -> [("#" <> v, nodeType t)]
              _        -> vs

    PRecord t pat -> do
        (p, vs) <- pat
        errs <- tryUnify t (tRecord (typeOf p))
        pure (recordPat (TypeInfo errs t []) p, vs)

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
    ODiv   t -> undefined -- TODO
    OPow   t -> undefined -- TODO
    OMod   t -> undefined -- TODO
    OLt    t -> opType t OLt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGt    t -> opType t OGt  (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLte   t -> opType t OLte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OGte   t -> opType t OGte (Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool))
    OLarr  t -> opType t OLarr (Forall [kTyp, kTyp, kTyp] [] ((tGen 1 `tArr` tGen 2) `tArr` (tGen 0 `tArr` tGen 1) `tArr` tGen 0 `tArr` tGen 2))
    ORarr  t -> opType t ORarr (Forall [kTyp, kTyp, kTyp] [] ((tGen 0 `tArr` tGen 1) `tArr` (tGen 1 `tArr` tGen 2) `tArr` tGen 0 `tArr` tGen 2))
    OFpip  t -> opType t OFpip (Forall [kTyp, kTyp] [] (tGen 0 `tArr` (tGen 0 `tArr` tGen 1) `tArr` tGen 1))
    OBpip  t -> opType t OBpip (Forall [kTyp, kTyp] [] ((tGen 0 `tArr` tGen 1) `tArr` tGen 0 `tArr` tGen 1))
    OOpt   t -> opType t OOpt (Forall [kTyp] [] (tApp kTyp (tCon kFun "Option") (tGen 0) `tArr` tGen 0 `tArr` tGen 0))
    OStr   t -> opType t OOpt (Forall [] [] (tString `tArr` tString `tArr` tString))
    ODot   t -> opType t ODot (Forall [kTyp, kTyp] [] ((tGen 0 `tArr` tGen 1) `tArr` tGen 0 `tArr` tGen 1))
    OField t -> opType t OField (Forall [kTyp, kTyp] [] (tCon kTyp "Symbol" `tArr` tGen 1 `tArr` tGen 0))

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
    pure [NonBooleanGuard (Ast (mapExprTag nodeType e)) | notNull errs]

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

fresh :: (MonadSupply Int m) => m Type
fresh = do
    s <- supply
    let st = showt s
    pure (tVar (kVar ("$n" <> st)) ("$v" <> st))

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
  -> m (ClassInfo Type (Ast (TypeInfo ())))
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
--test5expr = funExpr () [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "[]" []] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] [Choice [] (litExpr () (TBool True))] ]
--test5expr = varExpr () "(+)"
--test5expr = fixExpr () "foldSucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "Succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldSucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (letExpr () (BFun () "toInt" [varPat () "n"]) (appExpr () [ varExpr () "foldSucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr tInt (litExpr () (TInteger 0)) , varExpr () "n" ]) (appExpr () [ varExpr () "foldSucc" , lamExpr () [varPat () "n", varPat () "x"] (op2Expr () (OMul ()) (appExpr () [varExpr () "toInt", varExpr () "n"]) (varExpr () "x")) , annExpr tInt (litExpr () (TInteger 1)) , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]]]] ]))
--test5expr = letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (varExpr () "withDefault")
--test5expr = letExpr () (BFun () "withDefault" [varPat () "x", varPat () "y"]) (varExpr () "(+)") (varExpr () "withDefault")
--test5expr = letExpr () (BPat () (varPat () "f")) (varExpr () "(+)") (varExpr () "f")
--test5expr = letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "x"] (varExpr () "(+)")) (varExpr () "f")
--test5expr = letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "x"] (varExpr () "(+)")) (appExpr () [varExpr () "f", litExpr () (TInteger 9)])
--test5expr = letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (varExpr () "(+)") (appExpr () [varExpr () "f", litExpr () (TInteger 9)])
--test5expr = letExpr () (BFun () "f" [annPat tInt (varPat () "x"), varPat () "y"]) (varExpr () "(+)") (appExpr () [varExpr () "f", litExpr () (TInteger 9)])
--test5expr = letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (varExpr () "(+)") (appExpr () [varExpr () "f", litExpr () (TInteger 9)])
--test5expr = letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "x", varPat () "y"] (varExpr () "(+)")) (appExpr () [varExpr () "f", litExpr () (TInteger 9)])
--test5expr = lamExpr () [varPat () "x"] (patExpr () (varExpr () "x") [ Clause () (conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]) [Choice [] (litExpr () (TBool True))] , Clause () (conPat () "[]" []) [Choice [] (litExpr () (TBool True))] , Clause () (conPat () "(::)" [varPat () "z", varPat () "zs"]) [Choice [] (litExpr () (TBool True))] ])
--test5expr = appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ]
--test5expr = (appExpr () [lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))), recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])
--test5expr = fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 2)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Choice [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () (anyPat ()) [Choice [] (litExpr () (TInteger 0))] ])))
--test5expr = letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TInteger 1))) (conExpr () "{}" []))) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInteger 3))) (appExpr () [varExpr () "_#", varExpr () "r"])))))
--test5expr = let testList = annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "map" [varPat () "f", varPat () "ys"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], varExpr () "a"])] , Clause () [conPat () "Nil'" []] [Choice [] (conExpr () "[]" [])] ] ]) (varExpr () "ys")) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , testList ])))
--test5expr = lamExpr () [recordPat () (varPat () "z")] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z")))
--test5expr = lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z"))
--test5expr = letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] ]) (varExpr () "withDefault")
--test5expr = appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ]
--test5expr = (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
--test5expr = op2Expr () (ODot ()) (varExpr () "c") (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (rowExpr () "b" (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" [])) (conExpr () "{}" [])) (conExpr () "{}" [])))))
--test5expr = op2Expr () (ODot ()) (varExpr () "c") (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (recordExpr () (rowExpr () "b" (recordExpr () (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" []))) (conExpr () "{}" []))) (conExpr () "{}" [])))))
--test5expr = appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ]
--test5expr = op2Expr () (ODot ()) (varExpr () "c") (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (recordExpr () (rowExpr () "b" (recordExpr () (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" []))) (conExpr () "{}" []))) (conExpr () "{}" [])))))
-- test5expr = fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 2)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Choice [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () (anyPat ()) [Choice [] (litExpr () (TInteger 0))] ])))
--test5expr = letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TInteger 1))) (conExpr () "{}" []))) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInteger 3))) (appExpr () [varExpr () "_#", varExpr () "r"])))))
--test5expr = (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EAnn (Fix (TApp (Fix (KVar "k15")) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KCon "*")))) "List")) (Fix (TCon (Fix (KCon "*")) "Int")))) (Fix (EList () [Fix (ELit () (TInteger 1))])))) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PCon () "(::)" [Fix (PVar () "x"),Fix (PAny ())]), clauseChoices = [Choice [Fix (EOp2 () (OEq ()) (Fix (EVar () "x")) (Fix (ELit () (TInteger 1))))] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]}]))))
--test5expr =
--            (appExpr () [ lamExpr () [varPat () "x", varPat () "y"] (patExpr () (tupleExpr () [varExpr () "x", varExpr () "y"]) [ Clause () (tuplePat () [annPat tInt (litPat () (TInteger 1)), varPat () "x"])  [ Choice [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TInteger 0))] (varExpr () "x") , Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () (anyPat ()) [ Choice [] (annExpr tInt (litExpr () (TInteger 100))) ] ]) , litExpr () (TInteger 1) , litExpr () (TInteger 5) ])
--test5expr = (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 1)))),Fix (ELit () (TInteger 2)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]}]))))
--test5expr = (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 5)))),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]}]))))
--test5expr = (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] , varExpr () "testList" ])))
--test5expr = (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Choice [] (litExpr () (TInteger 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TInteger 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "foo"), conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]]))
--test5expr = funExpr () [ Clause () [litPat () (TBool True), litPat () (TBool True)] [Choice [] (litExpr () (TInt 1))] , Clause () [litPat () (TBool False), litPat () (TBool False)] [Choice [] (litExpr () (TInt 2))] , Clause () [varPat () "x", varPat () "y"] [Choice [] (litExpr () (TInt 3))] ]

--test5expr = funExpr ()
--    [ Clause () [litPat () (TBool True), litPat () (TBool True)] [Choice [] (litExpr () (TInt 1))]
--    , Clause () [litPat () (TBool False), litPat () (TBool False)] [Choice [] (litExpr () (TInt 2))]
--    , Clause () [varPat () "x", varPat () "y"] [Choice [] (litExpr () (TInt 3))]
--    ]

--test5expr = funExpr ()
--    [ Clause () [litPat () (TBool True)] [Choice [] (litExpr () (TInt 1))]
--    , Clause () [litPat () (TBool False)] [Choice [] (litExpr () (TInt 2))]
----    , Clause () [varPat () "x", varPat () "y"] [Choice [] (litExpr () (TInt 3))]
--    ]

--test5expr = appExpr () [varExpr () "(+)", holeExpr (), holeExpr ()]

--test5expr =
--        appExpr ()
--            [ op2Expr () (OAdd ()) (holeExpr ()) (holeExpr ())
--            , annExpr tInt (litExpr () (TInteger 5))
--            , annExpr tInt (litExpr () (TInteger 5))
--            ]
--
--test5expr =
--        letExpr () (BFun () "f" [varPat () "x"])
--            (litExpr () (TInteger 11))
--            (lamExpr () [varPat () "x"]
--                (appExpr () [varExpr () "show", appExpr () [varExpr () "read", varExpr () "x"]]))

---- let
--test5expr = letExpr () (BFun () "f" [recordPat () (varPat () "z")]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z"))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])

--test5expr = appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ]


--        -- (({ a = a | z }) => z)({ a = 1, b = 2 })
--test5expr = appExpr () [lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z"), recordExpr () (rowExpr () "a" (litExpr () (TInteger 1)) (rowExpr () "b" (litExpr () (TInteger 2)) (conExpr () "{}" [])))]

--        -- let f(z) = { a = 1 : Int | z } in f({ b = 2 : Int })
--test5expr = letExpr ()
--    (BFun () "f" [varPat () "z"])
--    (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z")))
--    (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (conExpr () "{}" []))])

--test5expr = lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z")))

--test5expr = appExpr () [lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z"))), recordExpr () (conExpr () "{}" [])]

--test5expr =
--        (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z"))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))

test5expr =
        (letExpr () (BPat () (varPat () "foo")) (funExpr () [ Clause () [litPat () (TInteger 0)] [Choice [] (litExpr () (TInteger 1))] , Clause () [varPat () "n"] [Choice [] (litExpr () (TInteger 2))] ]) (appExpr () [varExpr () "foo", litExpr () (TInteger 1)]))

runBundle :: Text -> Bundle
runBundle input =
    case runParserStack annExprParser "" input of
        Left err -> traceShow "error" (error (show err))
        --Right expr -> traceShow expr (compileBundle expr)
        Right expr -> (compileBundle expr)

compileBundle :: ProgExpr () Type -> Bundle
compileBundle expr = Bundle
    { sourceExpr = expr
    , typedExpr  = c1
    , normalExpr = c2
    , stage1Expr = d
    , stage2Expr = f
    , stage3Expr = g
    , stage4Expr = h
    , coreExpr   = i
    , value      = j
    , context    = ctx
    , scheme     = scheme
    }
  where
    (a, (_, _, ctx)) = runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType expr)
    c :: ProgExpr TInfo Void
    c = runSupplyNats (runReaderT (exhaustivePatternsCheck (astExpr a)) testConstructorEnv)
    (c1, scheme) = runSupplyNats (runReaderT (ambiguityCheck ctx c) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))
    c2 = normalizeExpr c1
    d = stage1Translate c2
    e = runSupplyNats (runReaderT (stage2Translate d) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))
    f = translateLiteral e
    g = runSupplyNats (runReaderT (evalStateT (stage3Translate f) mempty) (mempty, (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)))
    h = runSupplyNats (stage4Translate g)
    i = coreTranslate h
    j = evalExpr i testEvalEnv


test5 :: IO ()
test5 = do

    liftIO $ LBS.writeFile "/home/laserpants/code/tau-tooling/src/tmp/bundle.json" (encodePretty' defConfig{ confIndent = Spaces 2 } (toRep bundle))
    -- astExpr a
  where
    (a, (_, _, ctx)) = runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType test5expr)

    c :: ProgExpr TInfo Void
    c = runReader (exhaustivePatternsCheck (astExpr a)) testConstructorEnv

    (c1, scheme) = runSupplyNats (runReaderT (ambiguityCheck ctx c) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))
    c2 = normalizeExpr c1

    d = stage1Translate c2

    e = runSupplyNats (runReaderT (stage2Translate d) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))

    f = translateLiteral e

    g = runSupplyNats (runReaderT (evalStateT (stage3Translate f) mempty) (mempty, (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)))

    h = runSupplyNats (stage4Translate g)

    i = coreTranslate h

    j = evalExpr i testEvalEnv

    bundle = Bundle
        { sourceExpr = test5expr
        --, typedExpr  = astExpr a
        , typedExpr  = c1
        , normalExpr = c2
        , stage1Expr = d
        , stage2Expr = f
        , stage3Expr = g
        , stage4Expr = h
        , coreExpr   = i
        , value      = j
        , context    = ctx
        , scheme     = scheme
        }

data Bundle = Bundle
    { sourceExpr  :: ProgExpr () Type
    , typedExpr   :: ProgExpr (TypeInfo [Error]) Void
    , normalExpr  :: ProgExpr (TypeInfo [Error]) Void
    , stage1Expr  :: Stage1Expr (TypeInfo [Error])
    , stage2Expr  :: Stage2Expr (TypeInfo [Error])
    , stage3Expr  :: Stage3Expr Type
    , stage4Expr  :: Stage4Expr Type
    , coreExpr    :: Core
    , value       :: Maybe (Tau.Eval.Value Eval)
    , context     :: Context
    , scheme      :: Scheme
    } deriving (Show, Eq)

instance ToRep Bundle where
    toRep Bundle{..} =
        object
            [ "source"  .= toRep sourceExpr
            , "typed"   .= toRep typedExpr
            , "normal"  .= toRep normalExpr
            , "stage1"  .= toRep stage1Expr
            , "stage2"  .= toRep stage2Expr
            , "stage3"  .= toRep stage3Expr
            , "stage4"  .= toRep stage4Expr
            , "core"    .= toRep coreExpr
            , "value"   .= toRep value
            , "context" .= toRep context
            , "scheme"  .= toRep scheme
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

    , ( "show"         , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` tString) )
    , ( "read"         , Forall [kTyp] [InClass "Read" 0] (tString `tArr` tGen 0) )
    ]

testClassEnv :: ClassEnv
testClassEnv = Env.fromList
    [ ( "Read"
        -- Interface
      , ( ClassInfo (InClass "Read" "a") []
            [ ( "read", tString `tArr` tVar kTyp "a"  )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) []
              [ ( "read", Ast (varExpr (TypeInfo () (tString `tArr` tString) []) "@Int.read") )
              ]
          ]
        )
      )
    , ( "Show"
        -- Interface
      , ( ClassInfo (InClass "Show" "a") []
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) []
              [ ( "show", Ast (varExpr (TypeInfo () (tInt `tArr` tString) []) "@Int.Show") )
              ]
          , ClassInfo (InClass "Show" tString) []
              [ ( "show", Ast (varExpr (TypeInfo () (tString `tArr` tString) []) "@String.id") )
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

testEvalEnv :: ValueEnv Eval
testEvalEnv = Env.fromList
    [ ( "_#"  , fromJust (evalExpr (cLam "?0" (cPat (cVar "?0") [(["#", "?1"], cVar "?1")])) mempty) )
    , ( "(.)" , fromJust (evalExpr (cLam "f" (cLam "x" (cApp [cVar "f", cVar "x"]))) mempty) )
    ]

--testx = (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 2)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Choice [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () (anyPat ()) [Choice [] (litExpr () (TInteger 0))] ]))))

testx :: ProgExpr () Type
testx =
    patExpr () (varExpr () "x")
        [ Clause () (conPat () "Some" [varPat () "x"])
            [ Choice [op2Expr () (OEq ()) (varExpr () "x") (litExpr () (TInteger 111))] (litExpr () (TInteger 4))
            , Choice [op2Expr () (OEq ()) (varExpr () "x") (litExpr () (TInteger 112))] (litExpr () (TInteger 5))
            , Choice [] (litExpr () (TInteger 6))
            ]
        , Clause () (conPat () "None" [])
            [ Choice [appExpr () [varExpr () "predicate", varExpr () "x"]] (litExpr () (TInteger 7))
            , Choice [] (litExpr () (TInteger 8))
            ]
        , Clause () (anyPat ())
            [ Choice [] (litExpr () (TInteger 9)) ]
        ]

testy :: ProgExpr () Type
testy =
    funExpr ()
        [ Clause () [conPat () "Some" [varPat () "x"]]
            [ Choice [op2Expr () (OEq ()) (varExpr () "x") (litExpr () (TInteger 111))] (litExpr () (TInteger 4))
            , Choice [op2Expr () (OEq ()) (varExpr () "x") (litExpr () (TInteger 112))] (litExpr () (TInteger 5))
            , Choice [] (litExpr () (TInteger 6))
            ]
        , Clause () [conPat () "None" []]
            [ Choice [appExpr () [varExpr () "predicate", varExpr () "x"]] (litExpr () (TInteger 7))
            , Choice [] (litExpr () (TInteger 8))
            ]
        , Clause () [anyPat ()]
            [ Choice [] (litExpr () (TInteger 9)) ]
        ]
