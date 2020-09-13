{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
module Tau.Type.Inference where

import Control.Arrow ((>>>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Either.Extra (mapLeft)
import Data.Foldable (foldrM)
import Tau.Env
import Tau.Expr
import Tau.Solver
import Tau.Type
import Tau.Util
import qualified Tau.Env as Env

data TypeError
    = UnboundVariable Name
    | CannotSolve
    | UnificationError UnificationError
    | EmptyMatchStatement
    deriving (Show, Eq)

type TypeAssumption = Assumption Type

type InferTypeStack a = ExceptT TypeError (ReaderT Monoset (Supply Name)) a

newtype InferType a = InferType { unInferType :: InferTypeStack a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError TypeError
    , MonadSupply Name
    , MonadReader Monoset )

instance MonadFail InferType where
    fail _ = throwError CannotSolve

runInferType :: Env Scheme -> Expr -> Either TypeError (Type, Substitution Type, [TyClass])
runInferType env = runInfer . inferType env

runInfer :: InferType a -> Either TypeError a
runInfer = unInferType
    >>> runExceptT
    >>> flip runReaderT (Monoset mempty)
    >>> flip evalSupply (nameSupply "a")

liftErrors :: (MonadError TypeError m) => (ExceptT UnificationError m) a -> m a
liftErrors = runExceptT
    >>> (mapLeft UnificationError <$>)
    >>> (liftEither =<<)

inferType
  :: (MonadFail m, MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
  => Env Scheme
  -> Expr
  -> m (Type, Substitution Type, [TyClass])
inferType env expr = do
    (ty, as, cs) <- infer expr
    failIfExists (unboundVars env as)
    (sub, tycls) <- liftErrors (solveTypes (cs <> envConstraints as) )
    pure (ty, sub, tycls)
  where
    envConstraints :: [TypeAssumption] -> [TypeConstraint]
    envConstraints as = do
        (x, s) <- getAssumption <$> as
        (y, t) <- Env.toList env
        guard (x == y)
        pure (Explicit s t)

failIfExists :: (MonadError TypeError m) => [Name] -> m ()
failIfExists (var:_) = throwError (UnboundVariable var)
failIfExists _ = pure ()

unboundVars :: Env a -> [Assumption b] -> [Name]
unboundVars env as = Env.namesNotIn env (fst . getAssumption <$> as)

infer
  :: (MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
  => Expr
  -> m (Type, [TypeAssumption], [TypeConstraint])
infer = fmap to3 . runWriterT . cata alg where
    alg
      :: (MonadError TypeError m, MonadSupply Name m, MonadReader Monoset m)
      => Algebra ExprF (WriterT [TypeConstraint] m (Type, [TypeAssumption]))
    alg = \case
        VarS name -> do
           beta <- varT <$> supply
           pure (beta, [Assumption (name, beta)])

        LamS name expr -> do
           var <- supply
           let beta = varT var
           (t1, a1) <- local (insertIntoMonoset var) expr
           tell [Equality t beta | (y, t) <- getAssumption <$> a1, name == y]
           pure (beta `arrT` t1, removeAssumption name a1)

        AppS exprs ->
           foldl1 inferApp exprs

        LitS prim -> do
           t <- inferPrim prim
           pure (t, [])

        LetS var expr body ->
           inferLet var expr body False

        RecS var expr body ->
           inferLet var expr body True

        IfS cond true false -> do
           (t1, a1) <- cond
           (t2, a2) <- true
           (t3, a3) <- false
           tell [Equality t1 tBool]
           tell [Equality t2 t3]
           pure (t2, a1 <> a2 <> a3)

        MatchS _ [] ->
           throwError EmptyMatchStatement

        LamMatchS [] ->
           throwError EmptyMatchStatement

        MatchS expr clss -> do
            beta <- varT <$> supply
            (t1, a1) <- expr
            as <- foldrM (inferClause beta t1) [] clss
            pure (beta, a1 <> as)

        LamMatchS clss -> do
            beta <- varT <$> supply
            zeta <- varT <$> supply
            as <- foldrM (inferClause beta zeta) [] clss
            pure (zeta `arrT` beta, as)

        OpS op ->
           inferOp op

        AnnS{} ->
           undefined  -- TODO

        ErrS ->
           pure (conT "", [])

inferClause
  :: (MonadSupply Name m, MonadReader Monoset m, MonadWriter [TypeConstraint] m)
  => Type
  -> Type
  -> (Pattern, m (Type, [TypeAssumption]))
  -> [TypeAssumption]
  -> m [TypeAssumption]
inferClause beta t (pat, expr) as = do
    (t1, a1) <- local (insertManyIntoMonoset vars) expr
    (t2, a2) <- inferPattern pat
    tell [Equality beta t1]
    tell [Equality t t2]
    tell (constraints a1 a2)
    pure (as <> removeManyAssumptions vars a1 <> removeManyAssumptions vars a2)

  where
    vars = patternVars pat
    constraints a1 a2 = do
        (y1, t1) <- getAssumption <$> a1
        (y2, t2) <- getAssumption <$> a2
        var <- vars
        guard (var == y1 && var == y2)
        pure (Equality t1 t2)

inferPattern :: (MonadSupply Name m) => Pattern -> m (Type, [TypeAssumption])
inferPattern = cata $ \case
    VarP var -> do
        beta <- varT <$> supply
        pure (beta, [Assumption (var, beta)])

    ConP name ps -> do
        beta <- varT <$> supply
        (ts, ass) <- (fmap unzip . sequence) ps
        pure (beta, Assumption (name, foldr arrT beta ts):concat ass)

    LitP prim -> do
        t <- inferPrim prim
        pure (t, [])

    AnyP -> do
        beta <- varT <$> supply
        pure (beta, [])

inferApp
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => m (Type, [TypeAssumption])
  -> m (Type, [TypeAssumption])
  -> m (Type, [TypeAssumption])
inferApp fun arg = do
    (t1, a1) <- fun
    (t2, a2) <- arg
    beta <- varT <$> supply
    tell [Equality t1 (t2 `arrT` beta)]
    pure (beta, a1 <> a2)

inferPrim :: (Monad m) => Prim -> m Type
inferPrim = pure . \case
    Unit      -> tUnit
    Bool{}    -> tBool
    Int{}     -> tInt
    Integer{} -> tInteger
    Float{}   -> tFloat
    Char{}    -> tChar
    String{}  -> tString

inferLet
  :: (MonadReader Monoset m, MonadWriter [TypeConstraint] m)
  => Name
  -> m (Type, [TypeAssumption])
  -> m (Type, [TypeAssumption])
  -> Bool
  -> m (Type, [TypeAssumption])
inferLet var expr body rec = do
    (t1, a1) <- expr
    (t2, a2) <- body
    set <- ask
    tell [Implicit t t1 set | (y, t) <- getAssumption <$> a1 <> a2, var == y]
    pure (t2, (if rec then removeAssumption var a1 else a1) <> removeAssumption var a2)

inferOp
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => OpF (m (Type, [TypeAssumption]))
  -> m (Type, [TypeAssumption])
inferOp = \case
    AddS e1 e2 -> op2 e1 e2 numericOp2
    SubS e1 e2 -> op2 e1 e2 numericOp2
    MulS e1 e2 -> op2 e1 e2 numericOp2
    DivS e1 e2 -> op2 e1 e2 numericOp2
    LtS e1 e2  -> op2 e1 e2 comparisonOp
    GtS e1 e2  -> op2 e1 e2 comparisonOp
    EqS e1 e2  -> op2 e1 e2 equalityOp
    OrS e1 e2  -> op2 e1 e2 logicalOp
    AndS e1 e2 -> op2 e1 e2 logicalOp
    NegS e     -> op1 e numericOp1
    NotS e     -> op1 e numericOp1

op1
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => m (Type, [TypeAssumption])
  -> Scheme
  -> m (Type, [TypeAssumption])
op1 e1 sig = do
    (t1, a1) <- e1
    beta <- varT <$> supply
    tell [Explicit (t1 `arrT` beta) sig]
    pure (beta, a1)

op2
  :: (MonadSupply Name m, MonadWriter [TypeConstraint] m)
  => m (Type, [TypeAssumption])
  -> m (Type, [TypeAssumption])
  -> Scheme
  -> m (Type, [TypeAssumption])
op2 e1 e2 sig = do
    (t1, a1) <- e1
    (t2, a2) <- e2
    beta <- varT <$> supply
    tell [Explicit (t1 `arrT` (t2 `arrT` beta)) sig]
    pure (beta, a1 <> a2)

numericOp1 :: Scheme
numericOp1 =
    Forall ["a"]
    [TyCl "Num" (varT "a")]
    (arrT (varT "a") (varT "a"))

numericOp2 :: Scheme
numericOp2 =
    Forall ["a"]
    [TyCl "Num" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") (varT "a")))

equalityOp :: Scheme
equalityOp =
    Forall ["a"]
    [TyCl "Eq" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") tBool))

comparisonOp :: Scheme
comparisonOp =
    Forall ["a"]
    [TyCl "Ord" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") tBool))

logicalOp :: Scheme
logicalOp =
    Forall []
    []
    (arrT tBool (arrT tBool tBool))
