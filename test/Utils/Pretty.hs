{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Utils.Pretty where

import Data.Text (Text)
import Tau.Type

_type :: Type -> Text
_type = \case
    TCon name  -> name
    TVar name  -> name
    TApp t1 t2 -> _type t1 <> " " <> _type t2
    TArr t1 t2 -> _type t1 <> " -> " <> _type t2
