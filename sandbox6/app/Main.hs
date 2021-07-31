{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
module Main where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Either.Extra (eitherToMaybe)
import Data.Fix (Fix(..))
import Data.Function ((&))
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Data.Tuple.Extra
import Data.Void
import Tau.Misc
import Tau.Util
import TextShow
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

main :: IO ()
main = print "done"

--

freshType :: (MonadSupply Int f m) => m Type
freshType = do
    s <- demand
    let st = showt s
    pure (tVar (kVar ("$k" <> st)) ("$a" <> st))

runTagTree :: ProgExpr t u -> ProgExpr Type u
runTagTree expr = runSupplyNats (tagTree expr)

tagTree :: (MonadSupply Int f m) => ProgExpr t u -> m (ProgExpr Type u)
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
        ERow   _ name e r       -> rowExpr   <$> freshType <*> pure name <*> e <*> r
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
        PRow   _ name p r       -> rowPat    <$> freshType <*> pure name <*> p <*> r
        PAnn   t p              -> annPat  t <$> p

    tagBinding = \case
        BPat _ p                -> BPat <$> freshType <*> tagPattern p
        BFun _ name ps          -> BFun <$> freshType <*> pure name <*> traverse tagPattern ps

    tagClause = \case
        Clause _ ps guards      -> Clause <$> freshType
                                          <*> traverse tagPattern ps
                                          <*> traverse sequence guards
    tagClause1 = \case
        Clause _ p guards       -> Clause <$> freshType
                                          <*> tagPattern p
                                          <*> traverse sequence guards
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

inferExprType
  :: ( MonadSupply Int f m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgExpr Type Type
  -> m (ProgExpr (TypeInfo [Error]) Void)
inferExprType = cata $ \case

    EVar t var -> do
--        ty <- lookupScheme var >>= either
--            (\e -> pure (TypeInfo [e] t []))
--            undefined -- instantiate
        --errs <- tryUnify t ty
        --pure (varExpr (TypeInfo errs t []) var)
        undefined

    ECon t con es ->
        undefined

    ELit t prim ->
        undefined

    EApp t es ->
        undefined

    EFix t name e1 e2 ->
        undefined

    ELam t ps e ->
        undefined

    EIf t e1 e2 e3 ->
        undefined

    EPat t e cs ->
        undefined

    ELet t bind e1 e2 ->
        undefined

    EFun t cs ->
        undefined

    EOp1 t op a ->
        undefined

    EOp2 t op a b ->
        undefined

    ETuple t es ->
        undefined

    EList t es ->
        undefined

    ERow t name e r ->
        undefined

    EHole t ->
        undefined

    EAnn t a ->
        undefined

inferPatternType
  :: ( MonadSupply Int f m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => ProgPattern Type Type
  -> m (ProgPattern (TypeInfo [Error]) Void)
inferPatternType = cata $ \case

    PVar _ var ->
        undefined

    PCon _ name ps ->
        undefined

    PAs _ name p ->
        undefined

    PLit _ prim ->
        undefined

    PAny _ ->
        undefined

    POr _ p q ->
        undefined

    PTuple _ ps ->
        undefined

    PList _ ps ->
        undefined

    PRow _ name p r ->
        undefined

    PAnn t p ->
        undefined

lookupScheme
  :: ( MonadSupply Int f m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Name
  -> m (Either Error Scheme)
lookupScheme name = do
    env <- askTypeEnv
    case Env.lookup name env of
        Nothing ->
            pure (Left (NotInScope name))

        Just scheme ->
            Right <$> applySubsTo scheme

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
  :: ( MonadSupply Int f m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Scheme
  -> m (Type, [Predicate])
instantiate (Forall kinds preds ty) = do
    names <- ("$v" <>) . showt <$$> demands (length kinds)
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
  :: ( MonadSupply Int f m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadState (Substitution Type, Substitution Kind, Context) m )
  => Type
  -> Type
  -> m [Error]
tryUnify t1 t2 = go $ do
    ta <- applySubsTo t1
    tb <- applySubsTo t2
    (typeSub, kindSub) <- withExceptT UnificationError (unifyTypes ta tb)
    modify (first3 (typeSub <>))
    modify (second3 (kindSub <>))
    forM_ (Map.toList (getSub typeSub)) $ \(tv, ty) -> do
        env <- gets thd3
        propagateClasses ty (fromMaybe mempty (Env.lookup tv env))
  where
    go f = either pure (const []) <$> runExceptT f

propagateClasses
  :: ( MonadSupply Int f m
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
  :: ( MonadSupply Int f m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m
     , MonadError Error m )
  => Name
  -> Type
  -> m (ClassInfo Type (Ast (TypeInfo Void)))
lookupClassInstance name ty = do
    env <- asks getClassEnv
    (_, insts) <- liftMaybe (NoSuchClass name) (Env.lookup name env)
    info <- sequence [tryMatch i | i <- insts]
    msum info & maybe (throwError (MissingInstance name ty)) pure
  where
    tryMatch info@ClassInfo{..} = do
        sub <- eitherToMaybe <$> runExceptT (matchTypes (predicateType classSignature) ty)
        pure (applyBoth <$> sub <*> pure info)

-------------------------------------------------------------------------------

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

--

test2 = runSupplyNats subs
  where
    subs = unifyTypes2
        (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
        (tRow "shoeSize" tFloat (tVar kRow "r"))


--

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
unifyTypes2 a b = do
    runExceptT (unifyTypes a b) -- (+1) (0 :: Int)




-- tagTree :: (MonadSupply Int f m) => ProgExpr t u -> m (ProgExpr Name u)
-- tagTree = cata alg
--   where
--     alg expr = do
--         t <- freshType
--         case expr of
--
--             EVar _ var ->
--                 pure (varExpr t var)
--
--             ECon _ con es ->
--                 conExpr t con <$> sequence es
--
--             ELit _ prim ->
--                 pure (litExpr t prim)
--
--             EApp _ es ->
--                 appExpr t <$> sequence es
--
--             EFix _ name e1 e2 ->
--                 fixExpr t name <$> e1 <*> e2
--
--             ELam _ ps e ->
--                 lamExpr t <$> traverse tagPattern ps <*> e
--
--             EIf _ e1 e2 e3 ->
--                 ifExpr t <$> e1 <*> e2 <*> e3
--
--             EPat _ e cs ->
--                 patExpr t <$> e <*> traverse tagClause1 cs
--
--             ELet _ bind e1 e2 ->
--                 letExpr t <$> tagBinding bind <*> e1 <*> e2
--
--             EFun _ cs ->
--                 funExpr t <$> traverse tagClause cs
--
--             EOp1 _ op a ->
--                 op1Expr t <$> tagOp1 op <*> a
--
--             EOp2  _ op a b ->
--                 op2Expr t <$> tagOp2 op <*> a <*> b
--
--             ETuple _ es ->
--                 tupleExpr t <$> sequence es
--
--             EList _ es ->
--                 listExpr t <$> sequence es
--
--             ERow _ name e r ->
--                 rowExpr t name <$> e <*> r
--
--             EHole _ ->
--                 pure (holeExpr t)
--
--             EAnn t a ->
--                 annExpr t <$> a
--
--     tagPattern :: (MonadSupply Int f m) => ProgPattern t u -> m (ProgPattern Name u)
--     tagPattern = cata alg
--       where
--         alg pat = do
--             t <- freshType
--             case pat of
--
--                 PVar _ var ->
--                     pure (varPat t var)
--
--                 PCon _ name ps ->
--                     conPat t name <$> sequence ps
--
--                 PAs _ name p ->
--                     asPat t name <$> p
--
--                 PLit _ prim ->
--                     pure (litPat t prim)
--
--                 PAny _ ->
--                     pure (anyPat t)
--
--                 POr _ p q ->
--                     orPat t <$> p <*> q
--
--                 PTuple _ ps ->
--                     tuplePat t <$> sequence ps
--
--                 PList _ ps ->
--                     listPat t <$> sequence ps
--
--                 PRow _ name p r ->
--                     rowPat t name <$> p <*> r
--
--                 PAnn t p ->
--                     annPat t <$> p
--
--     tagBinding bind = do
--         t <- freshType
--         case bind of
--             BPat _ p       -> BPat t <$> tagPattern p
--             BFun _ name ps -> BFun t name <$> traverse tagPattern ps
--
--     tagClause (Clause _ ps guards) =
--         Clause <$> freshType <*> traverse tagPattern ps <*> traverse sequence guards
--
--     tagClause1 (Clause _ p guards) =
--         Clause <$> freshType <*> tagPattern p <*> traverse sequence guards
--
--     tagOp1 op = do
--         t <- freshType
--         pure $ case op of
--
--             ONeg   _ -> ONeg t
--             ONot   _ -> ONot t
--
--     tagOp2 op = do
--         t <- freshType
--         pure $ case op of
--
--             OEq    _ -> OEq    t
--             ONeq   _ -> ONeq   t
--             OAnd   _ -> OAnd   t
--             OOr    _ -> OOr    t
--             OAdd   _ -> OAdd   t
--             OSub   _ -> OSub   t
--             OMul   _ -> OMul   t
--             ODiv   _ -> ODiv   t
--             OPow   _ -> OPow   t
--             OMod   _ -> OMod   t
--             OLt    _ -> OLt    t
--             OGt    _ -> OGt    t
--             OLte   _ -> OLte   t
--             OGte   _ -> OGte   t
--             OLarr  _ -> OLarr  t
--             ORarr  _ -> ORarr  t
--             OFpip  _ -> OFpip   t
--             OBpip  _ -> OBpip   t
--             OOpt   _ -> OOpt   t
--             OStr   _ -> OStr   t
--             ODot   _ -> ODot   t
--             OField _ -> OField t

