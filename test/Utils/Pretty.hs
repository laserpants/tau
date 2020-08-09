{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Utils.Pretty where

import Data.Functor.Foldable
import Data.List (intersperse)
import Data.Text (Text, pack, unpack)
import Tau.Ast
import Tau.Pattern
import Tau.Prim
import Tau.Type
import Tau.Util
import qualified Data.Text as Text

_type :: Type -> Text
_type = \case
    TCon name  -> name
    TVar name  -> name
    TApp t1 t2 -> _type t1 <> " " <> _type t2
    TArr t1 t2 -> _type t1 <> " -> " <> _type t2

expr :: Expr -> Text
expr = cata alg
  where
    alg :: ExprF Text -> Text
    alg = \case
        VarS name ->
            name

        LamS name a ->
            "\\" <> name
                 <> " -> "
                 <> a

        AppS exprs ->
            Text.concat (intersperse " " exprs)

        LitS Unit ->
            "()"

        LitS (Bool bool) ->
            pack (show bool)

        LitS (Int n) ->
            pack (show n)

        LitS (Float r) ->
            pack (show r)

        LitS (Char c) ->
            pack (show c)

        LitS (String str) ->
            pack (show str)

        LitS prim ->
            pack (show prim)

        LetS pairs a ->
            "let" <> Text.concat (intersperse "; " $ binding <$> pairs)
                  <> " in "
                  <> a
              where
                binding (name, val) =
                    " " <> name
                        <> " = "
                        <> val

        IfS cond true false ->
            "if " <> cond <> " then " <> true <> " else " <> false

        CaseS expr clss ->
            "case " <> expr <> " of { " <> Text.concat (intersperse "; " $ clause <$> clss) <> " }"

        OpS ops ->
            op ops

        AnnS expr ty ->
            "TODO"

op :: OpF Text -> Text
op (AddS a b) = a <> " + " <> b
op (SubS a b) = a <> " - " <> b
op (MulS a b) = a <> " * " <> b
op (EqS a b) = a <> " == " <> b
op (LtS a b) = a <> " < " <> b
op (GtS a b) = a <> " > " <> b
op (NegS a) = "-" <> a
op (NotS a) = "not " <> a

clause :: (Pattern, Text) -> Text
clause (p, e) = cata alg p <> "=> " <> e
  where
    alg :: PatternF Text -> Text
    alg (VarP name)    = name <> " "
    alg (ConP name ps) = name <> " " <> Text.concat ps
    alg (LitP prim)    = pack (show prim) <> " "
    alg AnyP           = "_ "
