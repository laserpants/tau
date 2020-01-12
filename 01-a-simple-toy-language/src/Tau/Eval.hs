{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoMonadFailDesugaring #-}
module Tau.Eval where

import Control.Monad.Reader
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
        arg' <- eval arg
        let env' = Map.insert name arg' env
        local (const env') (eval body)

    Lam name body -> do
        env <- ask
        pure (Closure name body env)

    Let name expr body ->
        eval (App (Lam name body) expr)

    Lit val ->
        pure val

    Fix expr ->
        eval (App expr (Fix expr))

    If cond true false -> do
        Bool cond' <- eval cond
        eval (if cond' then true else false)

    Op op a b -> do
        Int a' <- eval a
        Int b' <- eval b
        pure (binop op a' b')


binop :: Op -> Integer -> Integer -> Value
binop Add a b = Int (a + b)
binop Mul a b = Int (a * b)
binop Sub a b = Int (a - b)
binop Eq a b = Bool (a == b)


runEval :: Env -> Var -> Expr -> ( Value, Env )
runEval env name expr =
    ( val, Map.insert name val env )
  where
    val = runReader (eval expr) env
