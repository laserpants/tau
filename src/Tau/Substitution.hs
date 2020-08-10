{-# LANGUAGE LambdaCase #-}
module Tau.Substitution where

import Data.Functor.Foldable
import Tau.Ast
import Tau.Core
import Tau.Pattern

substitute :: Name -> Expr -> Expr -> Expr
substitute name val = para alg where
    alg :: ExprF (Expr, Expr) -> Expr
    alg = \case
        VarS var
            | name == var -> val
            | otherwise -> varS var

        LamS var (expr, body)
            | name == var -> lamS var expr
            | otherwise -> lamS var body

        AppS exprs ->
            appS (snd <$> exprs)

        LitS prim ->
            litS prim

        LetS pairs body ->
            undefined

        IfS (_, cond) (_, true) (_, false) ->
            ifS cond true false

        CaseS expr clss ->
            undefined

        OpS op ->
            opS (snd <$> op)

        AnnS expr ty ->
            undefined  -- TODO

--substitute name val = cata $ \case
--    VarS var
--        | name == var -> val
--        | otherwise -> varS var
--
--    LamS var body
--        | name == var -> body
--        | otherwise -> lamS var body
--
--    AppS exprs ->
--        appS exprs
--
--    LitS prim ->
--        litS prim
--
--    LetS pairs body ->
--        letS pairs body
--
--    IfS cond true false ->
--        ifS cond true false
--
--    CaseS expr clss ->
--        caseS expr (xxx clss)
--
--    OpS op ->
--        opS op
--
--    AnnS expr ty ->
--        undefined  -- TODO
--
--xxx :: [(Pattern, Expr)] -> [(Pattern, Expr)]
--xxx = id
