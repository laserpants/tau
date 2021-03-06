{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval.Core where

import Control.Monad.Reader
import Data.Function ((&))
import Tau.Comp.Core
import Tau.Eval.Prim
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

type ValueEnv m = Env (Value m)

-- | An expression evaluates to a literal value, a fully applied data
-- constructor, a primitive function, or a closure.
data Value m
    = Value Literal
    | Data Name [Value m]
    | PrimFun Name Fun [Value m]
    | Closure Name (m (Value m)) ~(ValueEnv m)

instance Show (Value m) where
    show (Value lit) = 
        "Value " <> show lit
    show (Data name lit) = 
        "Data " <> show name <> " " <> show lit
    show (PrimFun name _ args) =
        "PrimFun " <> show name <> " " <> show args
    show Closure{} =
        "<<function>>"

instance Eq (Value m) where
    (==) (Value v) (Value w)             = v == w
    (==) (Data c vs) (Data d ws)         = c == d && vs == ws
    (==) (PrimFun f _ _) (PrimFun g _ _) = f == g
    (==) _ _                             = False

constructor :: (MonadReader (ValueEnv m) m) => Name -> Int -> Value m
constructor name 0 = Data name []
constructor name n = Closure v val mempty
  where
    vars@(v:vs) = 
        take n (nameSupply "%")
    val = (ini & foldr (\fun -> asks . Closure fun)) vs
    ini = do
        Env env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)

newtype Eval a = Eval { unEval :: ReaderT (ValueEnv Eval) Maybe a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFail
    , MonadReader (ValueEnv Eval) )

runEval :: Eval a -> ValueEnv Eval -> Maybe a
runEval = runReaderT . unEval 

evalExpr :: Core -> ValueEnv Eval -> Maybe (Value Eval)
evalExpr = runEval . eval

eval 
  :: (MonadFail m, MonadReader (ValueEnv m) m) 
  => Core
  -> m (Value m)
eval = cata $ \case
    CVar var ->
        evalVar var

    CLit lit ->
        pure (Value lit)

    CApp exs ->
        foldl1 evalApp exs

    CLet var e1 e2 -> do
        val <- e1
        local (Env.insert var val) e2 

    CLam var e1 ->
        asks (Closure var e1)

    CIf e1 e2 e3 -> do
        Value (LBool isTrue) <- e1
        if isTrue then e2 else e3

    CPat expr fields ->
        expr >>= evalPat fields

evalVar :: (MonadFail m, MonadReader (ValueEnv m) m) => Name -> m (Value m)
evalVar var = 
    case Text.stripPrefix "@" var of
        Just prim ->
            case Env.lookup prim primEnv of
                Just fun -> evalPrim prim fun []
                Nothing  -> do
                    traceShowM ("No primitive function " <> Text.unpack prim)
                    fail ("No primitive function " <> Text.unpack prim)

        Nothing -> do
            env <- ask
            unless (Env.isMember var env) (traceShowM ("Unbound identifier " <> var))
            maybe (fail "Unbound identifier") pure (Env.lookup var env)

evalPrim 
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => Name 
  -> Fun 
  -> [Value m] 
  -> m (Value m)
evalPrim name fun args
    | arity fun == length args = 
        Value . applyFun fun <$> traverse literal (reverse args)
    | otherwise = 
        pure (PrimFun name fun args)
  where
    literal (Value lit) = pure lit
    literal _ = fail "Runtime error (evalPrim)"

evalApp
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => m (Value m)
  -> m (Value m)
  -> m (Value m)
evalApp fun arg = fun >>= \case
    Closure var body closure -> do
        val <- arg
        local (Env.insert var val closure <>) body

    PrimFun name fun args -> do
        val <- arg
        evalPrim name fun (val:args)

evalPat 
  :: (MonadFail m, MonadReader (ValueEnv m) m)
  => [([Name], m (Value m))]
  -> Value m
  -> m (Value m)
evalPat [] _ = fail "Runtime error (evalMatch)"
evalPat ((p:ps, e):eqs) val =
    case val of
        Data con args | p == con -> 
            local (Env.inserts (zip ps args)) e

        _ -> 
            evalPat eqs val
