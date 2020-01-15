{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoMonadFailDesugaring #-}
module Tau.Eval where

import Control.Monad.Reader
import Debug.Trace
import Tau.Core
import Tau.Util
import qualified Data.Map as Map


type Eval = Reader Env


eval :: Expr -> Eval Value
eval = \case

    Var name -> do
        Just val <- asks $ Map.lookup name
        pure val

    App fun arg -> do
        Closure name body env <- eval fun
        arg_val <- eval arg
        let env_local = Map.insert name arg_val env
        local (const env_local) (eval body)

    Lam name body -> do
        env <- ask
        pure (Closure name body env)

    Let name expr body -> do
        eval (App (Lam name body) (Fix (Lam name expr)))

    Lit val ->
        pure val

    Fix expr ->
        eval (App expr (Fix expr))

    If cond true false -> do
        Bool cond_val <- eval cond
        eval (if cond_val then true else false)

    Op op a b -> do
        Int a_val <- eval a
        Int b_val <- eval b
        pure (binop op a_val b_val)


binop :: Op -> Integer -> Integer -> Value
binop Add a b = Int (a + b)
binop Mul a b = Int (a * b)
binop Sub a b = Int (a - b)
binop Eq a b = Bool (a == b)


runEval :: Env -> Name -> Expr -> ( Value, Env )
runEval env name expr =
    ( val, Map.insert name val env )
  where
    val = runReader (eval expr) env
