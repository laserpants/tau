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
import Data.Foldable
import Data.Either (lefts)
import Data.Either.Extra (mapLeft)
import Data.Function ((&))
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
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Ast t 
  -> m (Ast (TypeInfo [Error]))
inferAst = undefined

inferExpr
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => ProgExpr t 
  -> m (ProgExpr (TypeInfo [Error]))
inferExpr = cata $ \expr -> do
    newTy <- newTVar kTyp
    case expr of

        EVar _ var -> do
            (var, ti, __) <- inferNode newTy $ do
                ty <- lookupScheme var >>= instantiate
                unifyThis ty
                pure var

            pure (varExpr ti var)

        ECon _ con exprs -> do
            (es, ti, __) <- inferNode newTy $ do
                ty <- lookupScheme con >>= instantiate
                es <- traverse fooz2 exprs
                unify2W ty (foldr tArr newTy (typeOf <$> es))
                pure es

            pure (conExpr ti con es)

        ELit _ prim -> do
            (prim, ti, _) <- inferNode newTy $ do
                ty <- instantiate (primType prim)
                unifyThis ty
                pure prim

            pure (litExpr ti prim)

        EApp _ exprs -> do
            (es, ti, _) <- inferNode newTy $ do
                es <- traverse fooz2 exprs
                case es of
                    []     -> pure ()
                    f:args -> unify2W f (foldr tArr newTy (typeOf <$> args))
                pure es

            pure (appExpr ti es)

        ELet _ bind e1 e2 -> do
            undefined

        EFix _ name e1 e2 -> do
            undefined

        ELam _ ps expr -> do
            undefined

        EIf _ e1 e2 e3 -> do
            undefined

        EPat _ es cs -> do
            undefined

        EFun _ eqs@(Clause _ ps _:_) -> do
            (es, ti, _) <- inferNode newTy $ do
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

                --es <- sequence (inferClause ts <$> eqs)
                
                -- Unify return type with rhs of arrow in clauses
                --forM_ (clauseGuards =<< es) (\(Guard _ e) -> unify2 ty e)
                ---- Check patterns' types
                --forM_ (clausePatterns <$> es) (\ps -> forM_ (zip ps ts) unifyPatterns)
                ----
                --insertPredicates (clausePredicates =<< es)
                --unify2 newTy (foldr tArr ty ts)
                --pure es

            pure (funExpr ti es)

--        EFun t eqs@(Clause ps _:_) -> do
--            ts <- newTVars kTyp (length ps)
--            es <- sequence (inferClause t ts <$> eqs)
--            -- Unify return type with rhs of arrow in clauses
--            forM_ (clauseGuards =<< es) (\(Guard _ e) -> e ## newTy)
--            -- Check patterns' types
--            forM_ (clausePatterns <$> es) (\ps -> forM_ (zip ps ts) (unifyPatterns t))
--            pure (funExpr (TypeInfo (foldr tArr newTy ts) (clausePredicates =<< es)) es)

        EOp1 _ op a -> 
            undefined

        EOp2 _ op a b -> 
            undefined

        ETuple _ es -> 
            undefined

        EList _ es -> 
            undefined

        ERecord _ row ->
            undefined

inferPattern
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m ) 
  => ProgPattern t 
  -> m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
inferPattern = cata $ \pat -> do
    newTy <- newTVar kTyp
    case pat of

        PVar _ var -> do
            (var, ti, vs) <- inferNode newTy $ do
                insertThis var
                pure var

            pure (varPat ti var, vs)

        PCon _ con pats -> do
            (ps, ti, vs) <- inferNode newTy $ do
                lookupConstructor con >>= \case
                    Nothing -> pure ()
                    Just (_, arity) -> do
                        -- The number of arguments must match constructor arity 
                        when (arity /= length pats) $
                            insertErrors [ConstructorPatternArityMismatch con arity (length pats)]

                ty <- lookupScheme con >>= instantiate
                ps <- traverse fooz pats

                unify2W ty (foldr tArr newTy (typeOf <$> ps))
                pure ps

            pure (conPat ti con ps, vs)

--            catchError 
--                (ty ## foldr tArr newTy (typeOf <$> ps))
--                (const $ failWithError (ConstructorPatternTypeMismatch con ty (typeOf <$> ps)) t)

        PLit _ prim -> do
            (prim, ti, vs) <- inferNode newTy $ do
                t <- instantiate (primType prim)
                unifyThis t
                pure prim

            pure (litPat ti prim, vs)

        PAs _ var pat -> do
            (p, ti, vs) <- inferNode newTy $ do
                p <- fooz pat
                insertThis var
                unifyThis (typeOf p)
                pure p

            pure (asPat ti var p, vs)

--            p <- pat
--            tell [(as, newTy)]
--            newTy ## p
--            pure (asPat (TypeInfo newTy (patternPredicates p)) as p)
--
        POr _ pat1 pat2 -> do
            ((p1, p2), ti, vs) <- inferNode newTy $ do
                p1 <- fooz pat1
                p2 <- fooz pat2
                unifyThis (typeOf p1)
                unifyThis (typeOf p2)
                pure (p1, p2)

            pure (orPat ti p1 p2, vs)

        PAny _ -> do
            (_, ti, vs) <- inferNode newTy $ do
                pure ()

            pure (anyPat ti, vs)

        PTuple t pats -> do
            (ps, ti, vs) <- inferNode newTy $ do
                ps <- traverse fooz pats
                unifyThis (tTuple (typeOf <$> ps))
                pure ps

            pure (tuplePat ti ps, vs)

--            ps <- sequence pats
--            catchError 
--                (newTy ## tTuple (typeOf <$> ps))
--                (throwError . setMeta t)
--            pure (tuplePat (TypeInfo newTy (patternPredicates =<< ps)) ps)

        PList t pats -> do
            (ps, ti, vs) <- inferNode newTy $ do
                ps <- traverse fooz pats
                t1 <- case ps of
                    []    -> newTVar kTyp
                    (p:_) -> pure (typeOf p)
                -- Unify list elements' types
                forM_ ps (unify2W t1)
                unifyThis (tList t1)
                pure ps

            pure (listPat ti ps, vs)

--            catchError 
--                (forM ps (t1 ##))
--                (const $ failWithError ListPatternTypeUnficationError t)
--            pure (listPat (TypeInfo newTy (patternPredicates =<< ps)) ps)

        PRecord t row -> do
            (fs, ti, vs) <- inferNode newTy $ do
                fs <- traverse fooz row
                unifyThis (tRecord (rowToType (typeOf <$> fs)))
                pure fs

            pure (recordPat ti fs, vs)

--            fs <- sequence row
--            catchError 
--                (newTy ## tRecord (rowToType (typeOf <$> fs)))
--                (throwError . setMeta t)
--            pure (recordPat (TypeInfo newTy (concat (concatRow (patternPredicates <$> fs)))) fs)

fooz 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m ) 
  => m (ProgPattern (TypeInfo [Error]), [(Name, Type)])
  -> WriterT Node m (ProgPattern (TypeInfo [Error]))
fooz pat = do
    (p, vs) <- lift pat
    insertPredicates (patternPredicates p)
    tellVars vs
    pure p

fooz2 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m ) 
  => m (ProgExpr (TypeInfo [Error]))
  -> WriterT Node m (ProgExpr (TypeInfo [Error]))
fooz2 expr = do
    e <- lift expr
    insertPredicates (exprPredicates e)
    pure e


insertThis
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m ) 
  => Name
  -> WriterT Node m ()
insertThis var = do 
    t <- newTVar kTyp
    tellVars [(var, t)]
    unifyThis t

inferOp1 = undefined

inferOp2 = undefined

inferClause
  :: ( Monoid t
     , Show t
     , MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => [Type]
  -> Clause t (ProgPattern t) (m (ProgExpr (TypeInfo [Error])))
  -> m (ProgClause (TypeInfo [Error]))
inferClause tys eq@(Clause _ ps _) = do
    newTy <- newTVar kTyp
    ((x, y), ti, _) <- inferNode newTy $ do
        (tps, vs) <- second concat . unzip <$> traverse inferPattern ps
        let schemes = toScheme <$$> vs
            Clause _ _ guards = local (second3 (Env.inserts schemes)) <$> eq
            (iffs, es) = unzip (guardPair <$> guards)
        -- Conditions must be Bool
        forM_ (concat iffs) unifyIffCondition 
        gs <- lift (traverse sequence guards)
        pure (tps, gs)

    pure (Clause ti x y)

--unifyPatterns
--  :: ( Typed u
--     , Typed v 
--     , MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
--     , MonadState (TypeSubstitution, Context) m ) 
--  => t
--  -> (u, v) 
--  -> m ()
--unifyPatterns = undefined

--unifyPatterns
--  :: ( Monoid t
--     , Show t
--     , Typed a
--     , Typed b 
--     , MonadSupply Name m
--     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
--     , MonadState (TypeSubstitution, Context) m
----     , MonadError (InferError t) m 
--     ) 
--  => t
--  -> (a, b) 
--  -> m ()
--unifyPatterns t (v1, v2) = 
--    undefined
--
----    catchError 
----        (v1 ## v2)
----        (const $ failWithError (ClausePatternTypeMismatch (typeOf v1) (typeOf v2)) t)
--
--unifyPatterns (a, b) = uncurry unify2W (a, b)

unifyIffCondition 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m ) 
  => m (ProgExpr (TypeInfo [Error])) 
  -> WriterT Node m ()
unifyIffCondition expr = lift expr >>= unify2W (tBool :: Type) 

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

inferNode
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m )
  => Type
  -> WriterT Node m a
  -> m (a, TypeInfo [Error], [(Name, Type)])
inferNode t w = do
    (a, (ts, vs, ps, e)) <- runWriterT w
    errs <- lefts <$> mapM (runUnify t) ts
    pure (a, TypeInfo t ps (e <> errs), vs)

runUnify 
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, ConstructorEnv) m
     , MonadState (TypeSubstitution, Context) m 
     , Typed u
     , Typed v )
  => u
  -> v
  -> m (Either Error ())
runUnify a b = runExceptT (unify2 a b)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--data InferError t = InferError 
--    { errorSub  :: TypeSubstitution
--    , errorCtx  :: Context
--    , errorType :: Error
--    , errorMeta :: t
--    } deriving (Show, Eq)
--
--setMeta :: t -> InferError t -> InferError t
--setMeta meta InferError{..} = InferError{ errorMeta = meta, .. }

-- Monad transformer stack

--type InferState    = StateT (TypeSubstitution, Context)
--type InferReader   = ReaderT (ClassEnv, TypeEnv, ConstructorEnv)
--type InferSupply   = SupplyT Name

runInferState :: (Monad m) => Context -> InferState m a -> m (a, (TypeSubstitution, Context))
runInferState context = flip runStateT (mempty, context)

runInferReader :: (Monad m) => ClassEnv -> TypeEnv -> ConstructorEnv -> InferReader m r -> m r
runInferReader e1 e2 e3 = flip runReaderT (e1, e2, e3)

runInferSupply :: (Monad m) => InferSupply m a -> m a
runInferSupply = flip evalSupplyT (numSupply "a")

--type InferExcept t = ExceptT (InferError t)
--
--runInferExcept :: InferExcept t m a -> m (Either (InferError t) a)
--runInferExcept = runExceptT

--runInferMaybe :: (Monoid t) => Maybe (Either (InferError t) a) -> Either (InferError t) a
--runInferMaybe = fromMaybe (Left (InferError mempty mempty (Err "Implementation error") mempty))

--type InferStack t = InferReader (InferState (InferSupply (InferExcept t Maybe)))

--runInfer 
--  ::(Monoid t) 
--  => Context 
--  -> ClassEnv 
--  -> TypeEnv 
--  -> ConstructorEnv 
--  -> InferStack t a 
--  -> Either (InferError t) (a, TypeSubstitution, Context)
--runInfer context classEnv typeEnv constructorEnv = 
--    runInferReader classEnv typeEnv constructorEnv
--    >>> runInferState context
--    >>> runInferSupply
--    >>> runInferExcept
--    >>> runInferMaybe
--    >>> fmap to

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Monad transformer stack

type InferState    = StateT (TypeSubstitution, Context)
type InferReader   = ReaderT (ClassEnv, TypeEnv, ConstructorEnv)
type InferSupply   = SupplyT Name
type InferStack a  = InferReader (InferState (InferSupply a))

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

--    >>> runInferExcept

-- (InferState (InferSupply (InferExcept t Maybe)))

--runInfer context classEnv typeEnv constructorEnv = 
--    runInferReader classEnv typeEnv constructorEnv
--    >>> runInferState context
--    >>> runInferSupply
--    >>> runInferExcept
--    >>> runInferMaybe
--    >>> fmap to
