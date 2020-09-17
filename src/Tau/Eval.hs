{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Functor.Foldable
import Tau.Env
import Tau.Expr
import Tau.Util
import Tau.Value
import qualified Data.Map.Strict as Map
import qualified Tau.Env as Env

newtype Eval a = Eval { unEval :: ReaderT (ValueEnv Eval) Maybe a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFix
    , MonadFail
    , MonadReader (ValueEnv Eval) )

evalExpr :: Expr -> ValueEnv Eval -> Maybe (Value Eval)
evalExpr = runReaderT . unEval . eval

eval :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m) => Expr -> m (Value m)
eval = cata $ \case
    VarS name ->
        evalVar name

    LamS name expr ->
        asks (Closure name expr)

    AppS exprs ->
        foldl1 evalApp exprs

    LitS prim ->
        pure (Value prim)

    AtomS atom ->
        pure (Value (String atom))

    LetS var expr body -> do
        val <- expr
        local (Env.insert var val) body

    LetRecS var expr body -> do
        val <- mfix (\val -> local (Env.insert var val) expr)
        local (Env.insert var val) body

    IfS cond true false -> do
        Value (Bool isTrue) <- cond
        if isTrue then true else false

    MatchS expr clss ->
        expr >>= evalMatch clss

    LamMatchS clss ->
        asks (Closure "$" (evalVar "$" >>= evalMatch clss))

    OpS op ->
        evalOp op

    StructS expr -> 
        Record <$> expr

    AnnS expr _ ->
        expr

    ErrS ->
        fail "Runtime error (1)"

evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
evalVar name = do
    env <- ask
    maybe (fail "Unbound identifier") pure (Env.lookup name env)

evalMatch
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => [MatchClause (m (Value m))]
  -> Value m
  -> m (Value m)
evalMatch [] _ = fail "Runtime error (2)"
evalMatch ((match, expr):cs) val =
    case unfix match of
        AnyP ->
            expr

        VarP var ->
            local (Env.insert var val) expr

        con ->
            case matched con val of
                Just pairs ->
                    local (Env.insertMany pairs) expr

                Nothing ->
                    evalMatch cs val

matched :: PatternF Pattern -> Value m -> Maybe [(Name, Value m)]
matched (ConP n ps) (Data m vs) | n == m = Just (zip (getVarName <$> ps) vs)
matched _ _ = Nothing

getVarName :: Pattern -> Name
getVarName (Fix (VarP name)) = name
getVarName _                 = "Runtime error (3)"

evalApp
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => m (Value m)
  -> m (Value m)
  -> m (Value m)
evalApp fun arg = do
    Closure var body (Env closure) <- fun
    val <- arg
    local (const (Env (Map.insert var val closure))) body

evalOp :: (MonadFail m, MonadReader (ValueEnv m) m) => OpF (m (Value m)) -> m (Value m)
evalOp = \case
    AddS a b -> numOp (+) a b
    SubS a b -> numOp (-) a b
    MulS a b -> numOp (*) a b
    DivS a b -> do
        Value v <- a
        Value w <- b
        case (v, w) of
            (Int m, Int n) ->
                int (m `div` n)

            (Float p, Float q) ->
                float (p / q)

            _ -> fail "Type mismatch"

    EqS a b  -> do
        Value val1 <- a
        Value val2 <- b
        case (val1, val2) of
            (Int m, Int n) ->
                bool (m == n)

            (Bool x, Bool y) ->
                bool (x == y)

            (Unit, Unit) ->
                bool True

            _ -> fail "Type mismatch"

    NeqS a b  -> do
        Value val1 <- a
        Value val2 <- b
        case (val1, val2) of
            (Int m, Int n) ->
                bool (m /= n)

            (Bool x, Bool y) ->
                bool (x /= y)

            (Unit, Unit) ->
                bool False

            _ -> fail "Type mismatch"


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

            _ -> fail "Type mismatch"

    NotS a -> do
        Value (Bool b) <- a
        bool (not b)

    OrS a b -> do
        Value (Bool l) <- a
        Value (Bool r) <- b
        bool (l || r)

    AndS a b -> do
        Value (Bool l) <- a
        Value (Bool r) <- b
        bool (l && r)

    DotS a b ->
        evalApp b a

    CmpS a b ->
        asks (Closure "$" (evalVar "$" >>= evalApp a . evalApp b . pure))

  where
    numOp op a b = do
        Value (Int m) <- a
        Value (Int n) <- b
        int (m `op` n)

    bool  = pure . Value . Bool
    int   = pure . Value . Int
    float = pure . Value . Float
