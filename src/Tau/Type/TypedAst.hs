{-# LANGUAGE TypeOperators #-}
module Tau.Type.TypedAst where

import Control.Arrow ((>>>))
import Data.Functor.Const (Const(..))
import Data.Functor.Foldable (Fix(..), cata)
import Tau.Ast (ExprF)
import Tau.Type (Type)
import Tau.Type.Substitution (Substitutable, apply)
import Tau.Util ((:*:)(..))

type TypedExprF = Const Type :*: ExprF

newtype TypedExpr = TypedExpr { runTypedExpr :: Fix TypedExprF }
    deriving (Eq, Show)

instance Substitutable TypedExpr where
    apply sub = runTypedExpr >>> cata alg >>> TypedExpr
      where
        alg (Const ty :*: expr) = Fix (Const (apply sub ty) :*: expr)
