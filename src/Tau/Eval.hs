{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Functor.Foldable
import Tau.Ast
import Tau.Core
import Tau.Pattern
import Tau.Prim
import Tau.Value
import qualified Data.Map.Strict as Map

data EvalError
    = RuntimeError
    | UnboundVariable Name
    | TypeMismatch
    deriving (Show, Eq)

type EvalTStack m a = ReaderT (Env Eval) (ExceptT EvalError m) a

newtype EvalT m a = EvalT { unEvalT :: EvalTStack m a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader (Env Eval)
    , MonadError EvalError )

instance (Monad m) => MonadFail (EvalT m) where
    fail = const (throwError RuntimeError)

type Eval = EvalT Identity

runEvalT :: EvalT m a -> Env Eval -> m (Either EvalError a)
runEvalT a = runExceptT . runReaderT (unEvalT a)

evalExpr :: Env Eval -> Expr -> Either EvalError (Value Eval)
evalExpr env expr = runIdentity (runEvalT (eval expr) env)

evalMaybe :: (MonadFail m, MonadError EvalError m, MonadReader (Env m) m) => EvalError -> Maybe (Value m) -> m (Value m)
evalMaybe err = maybe (throwError err) pure

eval :: (MonadFail m, MonadError EvalError m, MonadReader (Env m) m) => Expr -> m (Value m)
eval = cata alg

alg :: (MonadFail m, MonadError EvalError m, MonadReader (Env m) m) => ExprF (m (Value m)) -> m (Value m)
alg = \case
    VarS name -> do
        env <- ask
        evalMaybe (UnboundVariable name) (Map.lookup name env)

    LamS name expr ->
        asks (Closure name expr)

    AppS exprs ->
        foldl1 evalApp exprs

    LitS prim ->
        pure (Value prim)

    LetS var expr body -> do
        val <- expr
        local (Map.insert var val) body

    IfS cond true false -> do
        Value (Bool isTrue) <- cond
        if isTrue then true else false

    CaseS expr clss -> do
        val <- expr
        evalCase val clss

    OpS op ->
        evalOp op

    AnnS expr ty ->
        -- TODO
        undefined

    Err ->
        throwError RuntimeError

evalCase :: (MonadFail m, MonadError EvalError m, MonadReader (Env m) m) => Value m -> [(Pattern, m (Value m))] -> m (Value m)
evalCase _ [] = throwError RuntimeError
evalCase val ((match, expr):cs) =
    case unfix match of
        AnyP ->
            expr

        VarP var ->
            local (Map.insert var val) expr

        con ->
            case matched con val of
                Just pairs ->
                    local (insertMany pairs) expr

                Nothing ->
                    evalCase val cs

insertMany :: [(Name, Value m)] -> Env m -> Env m
insertMany = flip (foldr (uncurry Map.insert))

matched :: PatternF (Fix PatternF) -> Value m -> Maybe [(Name, Value m)]
matched (ConP n ps) (Data m vs) | n == m = Just (zip (simple ps) vs)
matched _ _ = Nothing

simple :: [Pattern] -> [Name]
simple = fmap (\(Fix (VarP name)) -> name)

evalApp :: (MonadFail m, MonadError EvalError m, MonadReader (Env m) m) => m (Value m) -> m (Value m) -> m (Value m)
evalApp fun arg = do
    Closure var body closure <- fun
    val <- arg
    local (const (Map.insert var val closure)) body

evalOp :: (MonadFail m, MonadError EvalError m, MonadReader (Env m) m) => OpF (m (Value m)) -> m (Value m)
evalOp = \case
    AddS a b -> numOp (+) a b
    SubS a b -> numOp (-) a b
    MulS a b -> numOp (*) a b
    EqS a b  -> do
        Value val1 <- a
        Value val2 <- b
        case (val1, val2) of
            (Int m, Int n) ->
                bool (m == n)

            (Bool a, Bool b) ->
                bool (a == b)

            (Unit, Unit) ->
                bool True

            _ -> throwError TypeMismatch


    LtS a b -> do
        Value (Int m) <- a
        Value (Int n) <- b
        bool (m < n)

    GtS a b -> do
        Value (Int m) <- a
        Value (Int n) <- b
        bool (m > n)

    NegS a -> do
        Value val <- a
        case val of
            Int n ->
                int (negate n)

            Float p ->
                float (negate p)

            _ -> throwError TypeMismatch

    NotS a -> do
        Value (Bool b) <- a
        bool (not b)

  where
    numOp op a b = do
        Value (Int m) <- a
        Value (Int n) <- b
        int (op m n)

    bool  = pure . Value . Bool
    int   = pure . Value . Int
    float = pure . Value . Float
