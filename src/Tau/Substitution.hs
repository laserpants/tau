{-# LANGUAGE LambdaCase #-}
module Tau.Substitution where

import Data.Functor.Foldable
import Debug.Trace
import Tau.Ast
import Tau.Core
import Tau.Pattern

substitute :: Name -> Expr -> Expr -> Expr
substitute name val = para alg where
    alg :: ExprF (Expr, Expr) -> Expr
    alg = \case
        VarS var
            | name == var -> val
            | otherwise   -> varS var

        LamS var (expr, body)
            | name == var -> lamS var expr
            | otherwise   -> lamS var body

        AppS exprs ->
            appS (snd <$> exprs)

        LitS prim ->
            litS prim

        LetS var body expr ->
            let get = if name == var then fst else snd
             in letS var (get body) (get expr)

        IfS (_, cond) (_, true) (_, false) ->
            ifS cond true false

        CaseS expr clss ->
            undefined

        OpS op ->
            opS (snd <$> op)

        AnnS expr ty ->
            undefined  -- TODO

--xxx :: [(Pattern, Expr)] -> [(Pattern, Expr)]
--xxx = id
