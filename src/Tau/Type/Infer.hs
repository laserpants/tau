{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE StrictData    #-}
{-# LANGUAGE TypeOperators #-}
module Tau.Type.Infer where

import Control.Arrow ((>>>))
import Control.Monad.Except (throwError)
import Data.Functor.Const
import Data.Functor.Foldable
import Data.Map.Strict (Map, notMember)
import Tau.Ast
import Tau.Type
import Tau.Type.Infer.Monad
import Tau.Type.Solver
import Tau.Type.Substitution
import Tau.Util
import qualified Data.Map.Strict as Map

type TypedExprF = Const Type :*: ExprF

newtype TypedExpr = TypedExpr { runTypedExpr :: Fix TypedExprF }
    deriving (Eq, Show)

instance Substitutable TypedExpr where
    apply sub = runTypedExpr >>> cata alg >>> TypedExpr 
      where
        alg (Const t :*: expr) = Fix (Const (apply sub t) :*: expr)

getType :: TypedExpr -> Type
getType = getConst . left . unfix . runTypedExpr

infer :: Expr -> Infer (TypedExpr, [Assumption], [Constraint])
infer = undefined

inferAlg 
    :: ExprF (Infer (Type, [Assumption], [Constraint])) 
    -> Infer (Type, [Assumption], [Constraint])
inferAlg = \case
    VarS name -> 
        undefined

    LamS name expr ->
        undefined

    AppS exprs ->
        undefined

    LitS prim ->
        undefined

    LetS pairs body ->
        undefined

    IfS cond true false ->
        undefined

    CaseS expr clss ->
        undefined

    OpS op ->
        undefined

    AnnS expr ty ->
        undefined

unboundVars :: Map Name a -> [Assumption] -> [Name]
unboundVars env as = filter (`notMember` env) (fst <$> as)

inferType :: Context -> Expr -> Infer TypedExpr
inferType (Context env) expr = do
    (ty, as, cs) <- infer expr
    case unboundVars env as of
        [] -> do
            sub <- solve (cs <> [Explicit s t | (x, s) <- as, (y, t) <- Map.toList env, x == y])
            pure (apply sub ty)

        (var:_) ->
            throwError (UnboundVariable var)
