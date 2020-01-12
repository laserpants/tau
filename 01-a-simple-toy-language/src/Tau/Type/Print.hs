{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Print where

import Tau.Type
import Data.Text (Text, concat)
import qualified Data.Text as Text


prnt :: Type -> Text
prnt t =
    case t of
        TyVar var ->
            var

        TyInt ->
            "Int"

        TyBool ->
            "Bool"

        TyArr t1 t2 ->
            Text.concat [ prnt t1, " -> ", prnt t2 ]
