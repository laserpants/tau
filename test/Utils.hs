{-# LANGUAGE LambdaCase #-}
module Utils where

import Data.Functor.Foldable
import Data.List (nub, elemIndex)
import Data.Maybe (fromJust)
import Tau.Ast
import Tau.Core
import Tau.Prim
import Tau.Pattern
import Tau.Type
import Test.Hspec
import qualified Data.Set.Monad as Set

pass :: Expectation
pass = pure ()

data TypeRep
    = ConRep Name
    | VarRep Int
    | ArrRep TypeRep TypeRep
    | AppRep TypeRep TypeRep
  deriving (Show, Eq)

canonical :: Type -> TypeRep
canonical t = fun t
  where
    fun = \case
        TCon con   -> ConRep con
        TArr t1 t2 -> ArrRep (fun t1) (fun t2)
        TApp t1 t2 -> AppRep (fun t1) (fun t2)
        TVar var   -> VarRep (fromJust (elemIndex var vars))
    vars = Set.toList (free t)

isoTypes :: Type -> Type -> Bool
isoTypes t u = canonical t == canonical u
