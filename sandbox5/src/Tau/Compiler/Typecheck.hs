{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Typecheck where

import Control.Arrow ((<<<), (>>>))
import Control.Monad.Except (MonadError, catchError, throwError, liftEither)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Except
import Control.Monad.Writer
import Data.Function ((&))
import Data.Maybe (fromMaybe)
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
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m )
  => Ast t 
  -> m (Ast TypeInfo)
inferAst = undefined

inferExpr
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m )
  => ProgExpr t 
  -> m (ProgExpr TypeInfo)
inferExpr = cata $ \expr -> do
    newTy <- newTVar kTyp
    case expr of

        EVar _ var -> do
            (ty, ps) <- lookupScheme var >>= instantiate
            ty ## newTy
            pure (varExpr (TypeInfo newTy ps) var)

        ELit _ prim -> do
            (t, ps) <- instantiate (primType prim)
            newTy ## t
            pure (litExpr (TypeInfo newTy ps) prim)

        EFun t eqs@(Clause ps _:_) -> do
            ts <- newTVars kTyp (length ps)
            es <- sequence (inferClause t ts <$> eqs)
            let ty = foldr tArr newTy ts
            -- Unify return type with rhs of arrow in clauses
            forM_ (clauseGuards =<< es) (\(Guard _ e) -> e ## newTy)
            -- Check patterns' types
            forM_ (clausePatterns <$> es) (\ps -> forM_ (zip ps ts) (unifyPatterns t))
            -- Collect predicates
            let preds = concat ((patternPredicates <$> concatMap clausePatterns es) <> (guardPredicates <$> concatMap clauseGuards es))
            pure (funExpr (TypeInfo ty preds) es)

inferPattern
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => ProgPattern t 
  -> WriterT [(Name, Type)] m (ProgPattern TypeInfo)
inferPattern = cata $ \pat -> do
    newTy <- newTVar kTyp
    case pat of

        PVar _ var -> do
            tell [(var, newTy)]
            pure (varPat (TypeInfo newTy []) var)

        PCon t con pats -> do
            arity <- snd <$> lookupConstructor con
            -- The number of arguments must match constructor arity 
            when (arity /= length pats) $
                failWithError (ConstructorPatternArityMismatch con arity (length pats)) t

            (ty, qs) <- lookupScheme con >>= instantiate
            ps <- sequence pats
            catchError 
                (ty ## foldr tArr newTy (typeOf <$> ps))
                (const $ failWithError (ConstructorPatternTypeMismatch con ty (typeOf <$> ps)) t)
            pure (conPat (TypeInfo newTy (qs <> (patternPredicates =<< ps))) con ps)

        PLit _ prim -> do
            (t, ps) <- instantiate (primType prim)
            newTy ## t
            pure (litPat (TypeInfo newTy ps) prim)

        PAs _ as pat -> do
            p <- pat
            tell [(as, newTy)]
            newTy ## p
            pure (asPat (TypeInfo newTy (patternPredicates p)) as p)

        POr _ pat1 pat2 -> do
            p1 <- pat1
            p2 <- pat2
            newTy ## p1
            newTy ## p2
            pure (orPat (TypeInfo newTy (patternPredicates p1 <> patternPredicates p2)) p1 p2)

        PAny _ ->
            pure (anyPat (TypeInfo newTy []))

        PTuple t pats -> do
            ps <- sequence pats
            catchError 
                (newTy ## tTuple (typeOf <$> ps))
                (throwError . setMeta t)
            pure (tuplePat (TypeInfo newTy (patternPredicates =<< ps)) ps)

        PList t pats -> do
            ps <- sequence pats
            t1 <- case ps of
                []    -> newTVar kTyp
                (p:_) -> pure (typeOf p)
            newTy ## tList t1
            catchError 
                (forM ps (t1 ##))
                (const $ failWithError ListPatternTypeUnficationError t)
            pure (listPat (TypeInfo newTy (patternPredicates =<< ps)) ps)

        PRecord t row -> do
            fs <- sequence row
            catchError 
                (newTy ## tRecord (rowToType (typeOf <$> fs)))
                (throwError . setMeta t)
            pure (recordPat (TypeInfo newTy (concat (concatRow (patternPredicates <$> fs)))) fs)

inferOp1 = undefined

inferOp2 = undefined

inferClause
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => t
  -> [Type]
  -> Clause (ProgPattern t) (m (ProgExpr TypeInfo))
  -> m (Clause (ProgPattern TypeInfo) (ProgExpr TypeInfo))
inferClause t tys eq@(Clause ps _) = do
    (tps, vs) <- runWriterT (traverse inferPattern ps)
    let schemes = toScheme <$$> vs
        Clause _ guards = local (second3 (Env.inserts schemes)) <$> eq
        (tests, es) = unzip (guardPair <$> guards)
    -- Conditions must be of type Bool
    forM_ (concat tests) (unifyCondition t)
    Clause tps <$> traverse sequence guards

unifyPatterns
  :: ( Monoid t
     , Show t
     , Typed a
     , Typed b 
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => t
  -> (a, b) 
  -> m ()
unifyPatterns t (v1, v2) = 
    catchError 
        (v1 ## v2)
        (const $ failWithError (ClausePatternTypeMismatch (typeOf v1) (typeOf v2)) t)

unifyCondition
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => t 
  -> m (ProgExpr TypeInfo) 
  -> m ()
unifyCondition t expr = do 
    e <- expr
    catchError 
        (e ## (tBool :: Type))
        (const $ failWithError (BadGuardCondition (typeOf e)) t)

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

errorSpec
  :: ( MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => Error
  -> t
  -> m (InferError t)
errorSpec err t = do
    (sub, context) <- get
    pure (InferError sub context err t)

failWithError
  :: ( MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => Error
  -> t
  -> m a
failWithError err t = errorSpec err t >>= throwError

instantiate 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
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

lookupConstructor
  :: ( Monoid t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => Name 
  -> m (Set Name, Int)
lookupConstructor con = do
    env <- asks thd3
    case Env.lookup con env of
        Nothing   -> failWithError (NoDataConstructor con) mempty
        Just info -> pure info

lookupScheme 
  :: ( Monoid t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m ) 
  => Name 
  -> m Scheme
lookupScheme name = do
    env <- asks snd3
    case Env.lookup name env of
        Nothing     -> failWithError (UnboundTypeIdentifier name) mempty
        Just scheme -> gets (apply . fst) <*> pure scheme

unified 
  :: ( Monoid t
     , MonadState (TypeSubstitution, Context) m 
     , MonadError (InferError t) m ) 
  => Type 
  -> Type 
  -> m TypeSubstitution
unified t1 t2 = do
    sub1 <- gets fst
    case unify (apply sub1 t1) (apply sub1 t2) of
        Left err   -> failWithError (CannotUnify err t1 t2) mempty
        Right sub2 -> pure (sub2 <> sub1)

(##)
  :: ( Monoid t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m
     , Typed a
     , Typed b ) 
  => a 
  -> b 
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
  :: ( Monoid t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError (InferError t) m )
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
  :: ( Monoid t
     , MonadError (InferError t) m
     , MonadState (TypeSubstitution, Context) m )
  => Name 
  -> Type 
  -> ClassEnv
  -> m (ClassInfo Type (Ast TypeInfo))
lookupClassInstance tc ty env = do
    err <- errorSpec (MissingClass tc) mempty
    (ClassInfo{..}, insts) <- liftMaybe err (Env.lookup tc env)
    msum [tryMatch i | i <- insts] &
        maybe (failWithError (MissingInstance tc ty) mempty) pure
  where
    tryMatch ci@ClassInfo{..} = 
        case match (predicateType classSignature) ty of
            Left{}    -> Nothing
            Right sub -> Just (apply sub ci)

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

data InferError t = InferError 
    { errorSub     :: TypeSubstitution
    , errorContext :: Context
    , errorType    :: Error
    , errorMeta    :: t
    } deriving (Show, Eq)

setMeta :: t -> InferError t -> InferError t
setMeta meta InferError{..} = InferError{ errorMeta = meta, .. }

-- Monad transformer stack

type InferState    = StateT (TypeSubstitution, Context)
type InferReader   = ReaderT (ClassEnv, TypeEnv, ConstructorEnv)
type InferSupply   = SupplyT Name
type InferExcept t = ExceptT (InferError t)

runInferState :: (Monad m) => Context -> InferState m a -> m (a, (TypeSubstitution, Context))
runInferState context = flip runStateT (mempty, context)

runInferReader :: (Monad m) => ClassEnv -> TypeEnv -> ConstructorEnv -> InferReader m r -> m r
runInferReader e1 e2 e3 = flip runReaderT (e1, e2, e3)

runInferSupply :: (Monad m) => InferSupply m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

runInferExcept :: InferExcept t m a -> m (Either (InferError t) a)
runInferExcept = runExceptT

runInferMaybe :: (Monoid t) => Maybe (Either (InferError t) a) -> Either (InferError t) a
runInferMaybe = fromMaybe (Left (InferError mempty mempty (Err "Implementation error") mempty))

type InferStack t = InferReader (InferState (InferSupply (InferExcept t Maybe)))

runInfer 
  ::(Monoid t) 
  => Context 
  -> ClassEnv 
  -> TypeEnv 
  -> ConstructorEnv 
  -> InferStack t a 
  -> Either (InferError t) (a, TypeSubstitution, Context)
runInfer context classEnv typeEnv constructorEnv = 
    runInferReader classEnv typeEnv constructorEnv
    >>> runInferState context
    >>> runInferSupply
    >>> runInferExcept
    >>> runInferMaybe
    >>> fmap to
