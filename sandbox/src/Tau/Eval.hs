{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval where

import Control.Monad.Reader
import Tau.Env
import Tau.Expr
import Tau.Util
import qualified Data.Map.Strict as Map
import qualified Tau.Env as Env

type ValueEnv m = Env (Value m)

data Value m
    = Value Literal
    | Data Name [Value m]
    | Closure Name (m (Value m)) ~(ValueEnv m)

instance Show (Value m) where
    show (Value lit) = 
        "Value " <> show lit
    show (Data name lit) = 
        "Data " <> show name <> " " <> show lit
    show Closure{} = 
        "<<function>>"

newtype Eval a = Eval { unEval :: ReaderT (ValueEnv Eval) Maybe a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFix
    , MonadFail
    , MonadReader (ValueEnv Eval) )

runEval :: Eval a -> ValueEnv Eval -> Maybe a
runEval = runReaderT . unEval 

evalExpr :: Expr t (SimpleRep t) Name -> ValueEnv Eval -> Maybe (Value Eval)
evalExpr = runEval . eval

eval 
  :: (MonadFix m, MonadFail m, MonadReader (ValueEnv m) m) 
  => Expr t (SimpleRep t) Name 
  -> m (Value m)
eval = cata $ \case
    EVar _ var -> 
        evalVar var

    ECon _ con exprs -> do
        foldl1 evalApp (evalVar con:exprs)

    ELit _ lit ->
        pure (Value lit)

    EApp _ exprs -> 
        foldl1 evalApp exprs

    ELet _ var expr1 expr2 -> do
        val <- expr1
        local (Env.insert var val) expr2

    ELam _ var expr ->
        asks (Closure var expr)

    EIf t cond true false -> do
        Value (LBool isTrue) <- cond
        if isTrue then true else false

    EMat t exs eqs -> 
        sequence exs >>= evalMatch eqs 

    EOp t op ->
        evalOp op

evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
evalVar var = do
    env <- ask
    unless (Env.isMember var env) (traceShowM ("Unbound identifier " <> var))
    maybe (fail "Unbound identifier") pure (Env.lookup var env)

evalApp
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => m (Value m)
  -> m (Value m)
  -> m (Value m)
evalApp fun arg = do
    Closure var body (Env closure) <- fun
    val <- arg
    local (const (Env (Map.insert var val closure))) body

evalOp :: (MonadFail m, MonadReader (ValueEnv m) m) => Op (m (Value m)) -> m (Value m)
evalOp = \case 
    OEq a b -> do
        Value e1 <- a
        Value e2 <- b
        pure (Value (LBool (e1 == e2)))

    OAnd a b -> do
        Value (LBool e1) <- a
        Value (LBool e2) <- b
        pure (Value (LBool (e1 && e2)))

    OOr a b -> do
        Value (LBool e1) <- a
        Value (LBool e2) <- b
        pure (Value (LBool (e1 || e2)))

evalMatch
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => [Equation (SimpleRep t) (m (Value m))]
  -> [Value m]
  -> m (Value m)
evalMatch [] _ = fail "Runtime error (evalMatch)"
evalMatch (Equation ps exs e:eqs) vals = 
    case tryEquation ps vals of
        Just pairs -> do
            conds <- traverse (local (Env.insertMany pairs)) exs
            if and (toBool <$> conds) 
                then local (Env.insertMany pairs) e
                else next
        Nothing ->
            next
  where
    next = evalMatch eqs vals
    toBool (Value (LBool b)) = b
    toBool _ = error "Runtime error (toBool)"

tryEquation 
  :: (MonadFail m, MonadReader (ValueEnv m) m) 
  => [SimpleRep t] 
  -> [Value m] 
  -> Maybe [(Name, Value m)]
tryEquation xs ys = cata alg (zip xs ys)
  where
    alg :: Algebra (ListF (SimpleRep t, Value m)) (Maybe [(Name, Value m)])
    alg = \case 
        Cons (PVar _ var, val) xs -> 
            Just [(var, val)] <> xs

        Cons (PCon _ con1 ps, Data con2 args) xs 
            | con1 == con2 -> (<>) <$> Just (zip ps args) <*> xs
            | otherwise    -> Nothing

        Cons _ xs -> 
            error "Incompatible patterns"

        Nil -> 
            Just []
