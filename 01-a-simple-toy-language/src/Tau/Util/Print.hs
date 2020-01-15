{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Util.Print where

-- | Utilities for pretty printing

import Data.Text (Text)
import Data.Text.Lazy (toStrict)
import Formatting (format)
import Tau.Core (Value(..))
import Tau.Type (Type(..))
import qualified Data.Text as Text
import qualified Formatting


value :: Value -> Text
value = \case

    Int n ->
        toStrict (format Formatting.int n)

    Bool False ->
        "False"

    Bool True ->
        "True"

    String str ->
        str

    Char char ->
        Text.singleton char

    Unit ->
        "()"

    Closure{} ->
        "<function>"


type_ :: Type -> Text
type_ = \case

    TyVar var ->
        var

    TyCon con ->
        con

    TyArr t1 t2 ->
        Text.concat [ type_ t1, " -> ", type_ t2 ]
