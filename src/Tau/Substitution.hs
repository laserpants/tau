{-# LANGUAGE LambdaCase #-}
module Tau.Substitution where

import Data.Functor.Foldable
import Tau.Ast
import Tau.Core

substitute :: Name -> Expr -> Expr -> Expr
substitute name val = cata $ \case
    VarS var
        | name == var -> val
        | otherwise -> varS var

    LamS name expr -> 
        undefined

    AppS exprs ->
        undefined

    LitS prim -> 
        undefined

    LetS pairs body ->
        undefined

    IfS isTrue true false ->
        undefined

    CaseS expr clss -> 
        undefined

    OpS op ->
        undefined

    AnnS expr ty ->
        undefined
