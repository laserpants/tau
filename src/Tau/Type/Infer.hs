{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TypeOperators     #-}
module Tau.Type.Infer where

import Control.Arrow ((>>>))
import Control.Monad.Except (throwError)
import Control.Monad.Reader (local, ask)
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Functor.Const
import Data.Functor.Foldable
import Data.Map.Strict (Map, notMember)
import Data.Text (Text)
import Data.Tuple.Extra (fst3, first3)
import Tau.Ast
import Tau.Pattern
import Tau.Prim
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
        alg (Const ty :*: expr) = Fix (Const (apply sub ty) :*: expr)

getType :: TypedExpr -> Type
getType = getConst . left . unfix . runTypedExpr

infer :: Expr -> Infer (TypedExpr, [Assumption], [Constraint])
infer = cata alg where
    toTypedExpr ty = TypedExpr . Fix . (Const ty :*:)
    alg expr =
        (fmap (runTypedExpr . fst3) >>> flip toTypedExpr >>> first3)
            <$> sequence expr
            <*> (expr |> fmap fmap fmap (first3 getType) |> inferExpr)

type InferType = Infer (Type, [Assumption], [Constraint])

inferExpr :: ExprF InferType -> InferType
inferExpr = \case
    VarS name -> do
        beta <- supply
        pure (beta, [(name, beta)], [])

    LamS name expr -> do
        beta@(TVar var) <- supply
        (t1, a1, c1) <- local (insertIntoMonoset var) expr
        pure ( TArr beta t1
             , removeAssumption name a1
             , c1 <> [Equality t beta | (y, t) <- a1, name == y] )

    AppS exprs ->
        foldl1 inferApp exprs

    LitS prim ->
        inferPrim prim

    LetS pairs body ->
        foldr inferLet body pairs

    IfS cond true false -> do
        (t1, a1, c1) <- cond
        (t2, a2, c2) <- true
        (t3, a3, c3) <- false
        pure ( t2
             , a1 <> a2 <> a3
             , c1 <> c2 <> c3 <> [Equality t1 tBool, Equality t2 t3] )

    CaseS expr clss -> 
        expr >>= inferClauses clss

    OpS op ->
        inferOp op

    AnnS expr ty -> do
        (t1, a1, c1) <- expr
        -- TODO
        undefined

inferPrim :: Prim -> InferType
inferPrim = \case
    Unit      -> pure (tUnit, [], [])
    Bool{}    -> pure (tBool, [], [])
    Int{}     -> pure (tInt, [], [])
    Integer{} -> pure (tInteger, [], [])
    Float{}   -> pure (tFloat, [], [])
    Char{}    -> pure (tChar, [], [])
    String{}  -> pure (tString, [], [])

inferClauses
    :: [(Pattern, InferType)]
    -> (Type, [Assumption], [Constraint])
    -> InferType
inferClauses clss (t, a, c) = do
    beta <- supply
    foldrM fun (beta, a, c) clss
  where
    fun :: (Pattern, InferType) 
        -> (Type, [Assumption], [Constraint]) 
        -> InferType
    fun (ptn, expr) (beta, as, cs) = do
        (t1, a1, c1) <- expr
        flip cata ptn $ \case
            VarP var ->
                pure ( beta
                     , as <> removeAssumption var a1
                     , cs <> c1
                          <> [Equality t1 beta]
                          <> [Equality t1 t' | (y, t') <- a1, var == y] )

            LitP prim -> do
                t0 <- fst3 <$> inferPrim prim
                pure ( beta
                     , as <> a1
                     , cs <> c1 <> [Equality t1 beta, Equality t0 t] )

            AnyP ->
                pure ( beta
                     , as <> a1
                     , cs <> c1 <> [Equality t1 beta] )

            ConP name ps -> do
                beta <- supply
                foldl1 inferApp (pure (beta, [(name, beta)], []):ps)

inferApp :: InferType -> InferType -> InferType
inferApp fun arg = do
    (t1, a1, c1) <- fun
    (t2, a2, c2) <- arg
    beta <- supply
    pure ( beta
         , a1 <> a2
         , c1 <> c2 <> [Equality t1 (TArr t2 beta)] )

inferLet :: (Name, InferType) -> InferType -> InferType
inferLet (var, expr) body = do
    (t1, a1, c1) <- expr
    (t2, a2, c2) <- body
    set <- ask
    pure ( t2
         , removeAssumption var a1 <> removeAssumption var a2
         , c1 <> c2 <> [Implicit t t1 set | (y, t) <- a1 <> a2, var == y] )

inferOp :: OpF InferType -> InferType
inferOp = \case
    AddS e1 e2 -> binOp e1 e2 tInt tInt
    SubS e1 e2 -> binOp e1 e2 tInt tInt
    MulS e1 e2 -> binOp e1 e2 tInt tInt
    LtS e1 e2 -> binOp e1 e2 tInt tBool
    GtS e1 e2 -> binOp e1 e2 tInt tBool
    NegS e -> unOp e tInt
    NotS e -> unOp e tBool
    EqS e1 e2 -> do
        (t1, a1, c1) <- e1
        (t2, a2, c2) <- e2
        beta <- supply
        pure ( beta
             , a1 <> a2
             , c1 <> c2 <> [Equality t1 t2, Equality beta tBool] )

unOp :: InferType -> Type -> InferType
unOp expr t = do
    (t1, a1, c1) <- expr
    beta <- supply
    pure (beta, a1, c1 <> [Equality (TArr t1 beta) (TArr t t)])

binOp :: InferType -> InferType -> Type -> Type -> InferType
binOp e1 e2 t0 t = do
    (t1, a1, c1) <- e1
    (t2, a2, c2) <- e2
    beta <- supply
    pure ( beta
         , a1 <> a2
         , c1 <> c2 <> [Equality (TArr t1 (TArr t2 beta)) (TArr t0 (TArr t0 t))] )

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

{-# ANN inferOp ("HLint: ignore Reduce duplication" :: Text) #-}
