{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Core.Print where

import Data.Text (Text, pack)
import Data.Text.Lazy (toStrict)
import Formatting (format)
import Tau.Core
import qualified Data.Text as Text
import qualified Formatting as Format


prnt :: Value -> Text
prnt = \case

    Int n ->
        toStrict (format Format.int n)

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
