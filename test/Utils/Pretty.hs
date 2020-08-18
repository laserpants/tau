{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Utils.Pretty where

import Data.Functor.Foldable
import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, unpack)
import Tau.Ast
import Tau.Pattern
import Tau.Prim
import Tau.Type
import Tau.Util
import Tau.Value
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

        LetS name expr body ->
            "let " <> name <> " = " <> expr <> " in " <> body

        IfS cond true false ->
            "if " <> cond <> " then " <> true <> " else " <> false

        CaseS expr [] ->
            "case {} of"

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
clause (p, e) = _pattern p <> " => " <> e

_pattern :: Pattern -> Text
_pattern = trim . cata alg where
    trim = dropPrefix . dropSuffix . Text.dropWhileEnd (== ' ')
    alg (VarP name)    = name <> " "
    alg (ConP name []) = name <> " "
    alg (ConP name ps) = "(" <> name <> " " <> Text.dropEnd 1 (Text.concat ps) <> ") "
    alg (LitP p)       = prim p <> " "
    alg AnyP           = "_ "

prim :: Prim -> Text
prim Unit        = "()"
prim (Bool b)    = pack (show b)
prim (Float r)   = pack (show r)
prim (Char c)    = pack (show c)
prim (Int n)     = pack (show n)
prim (Integer n) = pack (show n)
prim (String s)  = "\"" <> s <> "\""

dropPrefix :: Text -> Text
dropPrefix txt = fromMaybe txt $ Text.stripPrefix "(" txt

dropSuffix :: Text -> Text
dropSuffix txt = fromMaybe txt $ Text.stripSuffix ")" txt

patterns :: [Pattern] -> Text
patterns = Text.concat . intersperse "\n    - " . (:) "" . map _pattern

value :: Value m -> Text
value (Value p)        = prim p 
value (Data name args) = name <> " " <> Text.concat (intersperse " " (value <$> args))
value Closure{}        = "<<function>>"
