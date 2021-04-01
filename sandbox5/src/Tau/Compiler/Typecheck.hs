{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Typecheck where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (first, second)
import Tau.Compiler.Error
import Tau.Compiler.Substitution
import Tau.Compiler.Unification
import Tau.Env (Env(..))
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

inferAst
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m )
  => Ast t 
  -> m (Ast TypeInfo)
inferAst = undefined

inferPattern
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m ) 
  => ProgPattern t 
  -> WriterT [(Name, Type)] m (ProgPattern TypeInfo)
inferPattern = cata $ \pat -> do
    newTy <- newTVar kTyp
    case pat of

        PVar _ var -> do
            tell [(var, newTy)]
            pure (varPat (TypeInfo newTy []) var)

        PCon _ con pats -> do
            (ty, qs) <- lookupScheme con >>= instantiate
            ps <- sequence pats
            ty ## foldr tArr newTy (typeOf <$> ps)
            pure (conPat (TypeInfo newTy qs) con ps)

        PLit _ prim -> do
            (t, ps) <- instantiate (primType prim)
            newTy ## t
            pure (litPat (TypeInfo newTy ps) prim)

        PAs _ as pat -> do
            tell [(as, newTy)]
            asPat (TypeInfo newTy []) as <$> pat

        POr _ pat1 pat2 -> do
            p1 <- pat1
            p2 <- pat2
            newTy ## p1
            newTy ## p2
            pure (orPat (TypeInfo newTy []) p1 p2)

        PAny _ ->
            pure (anyPat (TypeInfo newTy []))

        PTuple _ pats -> do
            ps <- sequence pats
            newTy ## tTuple (typeOf <$> ps)
            pure (tuplePat (TypeInfo newTy []) ps)

        PList _ pats -> do
            ps <- sequence pats
            t1 <- case ps of
                []    -> newTVar kTyp
                (p:_) -> pure (typeOf p)
            newTy ## tList t1
            pure (listPat (TypeInfo newTy []) ps)

        PRecord _ row ->
            undefined

inferOp1 = undefined

inferOp2 = undefined

inferClause = undefined

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

instantiate 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m ) 
  => Scheme 
  -> m (Type, [Predicate])
instantiate (Forall kinds preds ty) = do
    names <- supplies (length kinds)
    let ts = zipWith tVar kinds names
        fn p@(InClass cl n) = 
            ( (names !! n, Set.singleton cl)
            , replaceBound ts <$> (tGen <$> p) )
        (pairs, ps) = unzip (fn <$> preds)
    modify (second (`insertAll` pairs))
    pure (replaceBound ts ty, ps)

insertAll :: Context -> [(Name, Set Name)] -> Context
insertAll = foldr (uncurry (Env.insertWith Set.union)) 

lookupScheme 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, e) m
     , MonadError Error m ) 
  => Name 
  -> m Scheme
lookupScheme name = do
    env <- asks snd 
    case Env.lookup name env of
        Nothing     -> throwError ("Unbound type identifier: " <> Text.unpack name)
        Just scheme -> gets (apply . fst) <*> pure scheme

unified 
  :: ( MonadState (TypeSubstitution, c) m 
     , MonadError Error m ) 
  => Type 
  -> Type 
  -> m TypeSubstitution
unified t1 t2 = do
    sub1 <- gets fst
    sub2 <- unify (apply sub1 t1) (apply sub1 t2)
    pure (sub2 <> sub1)

(##)
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError String m
     , Typed t
     , Typed u ) 
  => t -> u 
  -> m ()
(##) v1 v2 = do 
    sub <- unified (typeOf v1) (typeOf v2)
    modify (first (sub <>))
    forM_ (Map.toList (getSub sub)) (uncurry propagate)  
  where
    propagate tv ty = do
        env <- gets snd
        propagateClasses ty (fromMaybe mempty (Env.lookup tv env))

propagateClasses 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
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
        env <- asks fst
        ClassInfo{ classSuper = preds } <- liftEither (lookupClassInstance name ty env)
        sequence_ [propagateClasses t (Set.singleton a) | InClass a t <- preds]

lookupClassInstance 
  :: (MonadPlus m, MonadError String m) 
  => Name 
  -> Type 
  -> ClassEnv
  -> m (ClassInfo Type (Ast TypeInfo))
lookupClassInstance name ty env = do
    (ClassInfo{..}, insts) <- liftMaybe ("No class " <> Text.unpack name) (Env.lookup name env)
    catchError 
        (msum [tryMatch i | i <- insts]) 
        (const (throwError "Missing class instance")) -- TODO: insert type name
  where
    tryMatch ci@ClassInfo{..} = 
        (`apply` ci) <$> match (predicateType classSignature) ty

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

instance Substitutable (ClassInfo Type (Ast TypeInfo)) Void where
    apply sub ClassInfo{..} = 
        ClassInfo{ classSuper     = apply sub classSuper 
                 , classSignature = apply sub classSignature
                 , .. }

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Monad transformer stack

type InferState  = StateT (TypeSubstitution, Context)
type InferReader = ReaderT (ClassEnv, TypeEnv)
type InferSupply = SupplyT Name
type InferError  = ExceptT String

runInferState :: Context -> StateT (TypeSubstitution, Context) m a -> m (a, (TypeSubstitution, Context))
runInferState context = flip runStateT (mempty, context)

runInferReader :: a -> b -> ReaderT (a, b) m r -> m r
runInferReader a b = flip runReaderT (a, b)

runInferSupply :: (Monad m) => SupplyT Name m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

runInferError :: ExceptT e m a -> m (Either e a)
runInferError = runExceptT

runInferMaybe :: Maybe (Either Error a) -> Either Error a
runInferMaybe = fromMaybe (Left "Implementation error")

type InferStack = InferState (InferReader (InferSupply (InferError Maybe)))

runInfer :: Context -> ClassEnv -> TypeEnv -> InferStack a -> Either String (a, (TypeSubstitution, Context))
runInfer context classEnv typeEnv = 
    runInferState context
    >>> runInferReader classEnv typeEnv
    >>> runInferSupply
    >>> runInferError
    >>> runInferMaybe
