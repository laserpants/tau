{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Data.List (unzip4)
import Data.Tuple.Extra (first3)
import Tau.Ast
import Tau.Core
import Tau.Pattern
import Tau.Prim
import Tau.Type
import Tau.Type.Infer.Monad
import Tau.Type.Solver
import Tau.Type.Substitution
import Tau.Type.TypedAst
import qualified Data.Map.Strict as Map

type TExpr = Fix TypedExprF

type InferTExpr = Infer (TExpr, Type, [Assumption], [Constraint])

infer :: Expr -> Infer (TypedExpr, [Assumption], [Constraint])
infer = cata (fmap unfixt >>> alg) where
    alg = \case
        VarS name -> do
            beta <- supply
            pure ( beta >*< VarS name
                 , [(name, beta)]
                 , [] )

        LamS name expr -> do
            beta@(TVar var) <- supply
            (_expr, t1, a1, c1) <- local (insertIntoMonoset var) expr
            pure ( TArr beta t1 >*< LamS name _expr
                 , removeAssumption name a1
                 , c1 <> [Equality t beta | (y, t) <- a1, name == y] )

        AppS exprs -> do
            (_expr, _, as, cs) <- foldl1 inferApp exprs
            pure ( TypedExpr _expr, as, cs )

        LitS prim -> do
            t <- inferPrim prim
            pure ( t >*< LitS prim, [], [] )

        LetS var expr body -> do
            (_e1, t1, a1, c1) <- expr
            (_e2, t2, a2, c2) <- body
            set <- ask
            pure ( t2 >*< LetS var _e1 _e2
                 , removeAssumption var a1 <> removeAssumption var a2
                 , c1 <> c2 <> [Implicit t t1 set | (y, t) <- a1 <> a2, var == y] )

        IfS cond true false -> do
            (_cond, t1, a1, c1) <- cond
            (_true, t2, a2, c2) <- true
            (_false, t3, a3, c3) <- false
            pure ( t2 >*< IfS _cond _true _false
                 , a1 <> a2 <> a3
                 , c1 <> c2 <> c3 <> [Equality t1 tBool, Equality t2 t3] )

        CaseS _ [] ->
            throwError EmptyCaseStatement

        CaseS expr clss -> do
            beta <- supply
            (_expr, t1, a1, c1) <- expr
            (_clss, as, cs) <- foldrM (inferClause beta t1) ([], [], []) clss
            pure ( beta >*< CaseS _expr _clss
                 , a1 <> as
                 , c1 <> cs )

        OpS op ->
            inferOp op

        AnnS expr ty ->
            undefined  -- TODO

insertMany :: [Name] -> Monoset -> Monoset
insertMany = flip (foldr insertIntoMonoset)

getVars :: Pattern -> [Name]
getVars = cata alg where
    alg :: PatternF [Name] -> [Name]
    alg (VarP v)    = [v]
    alg (ConP _ ps) = concat ps
    alg _           = []

type Clause = (Pattern, TExpr)

inferClause
    :: Type
    -> Type
    -> (Pattern, InferTExpr)
    -> ([Clause], [Assumption], [Constraint])
    -> Infer ([Clause], [Assumption], [Constraint])
inferClause beta t (pttrn, expr) (ps, as, cs) = do
    (_expr, t1, a1, c1) <- local (insertMany vars) expr
    (t2, a2, c2) <- inferPattern pttrn
    pure ( (pttrn, _expr):ps
         , as <> removeMany vars a1
              <> removeMany vars a2
         , cs <> c1 <> c2
              <> [Equality beta t1, Equality t t2]
              <> [Equality t' t'' | (y1, t') <- a1, (y2, t'') <- a2, var <- vars, var == y1 && var == y2] )
  where
    vars = getVars pttrn

inferPattern :: Pattern -> Infer (Type, [Assumption], [Constraint])
inferPattern = cata $ \case
    VarP var -> do
        beta <- supply
        pure (beta, [(var, beta)], [])

    ConP name ps -> do
        beta <- supply
        (ts, ass, css) <- (fmap unzip3 . sequence) ps
        pure ( beta
             , concat ass <> [(name, foldr TArr beta ts)]
             , concat css )

    LitP prim -> do
        t <- inferPrim prim
        pure (t, [], [])

    AnyP -> do
        beta <- supply
        pure (beta, [], [])

inferApp :: InferTExpr -> InferTExpr -> InferTExpr
inferApp fun arg = do
    (_e1, t1, a1, c1) <- fun
    (_e2, t2, a2, c2) <- arg
    beta <- supply
    pure ( Fix (Const beta :*: AppS [_e1, _e2])
         , beta
         , a1 <> a2
         , c1 <> c2 <> [Equality t1 (TArr t2 beta)] )

inferPrim :: Prim -> Infer Type
inferPrim = pure . \case
    Unit      -> tUnit
    Bool{}    -> tBool
    Int{}     -> tInt
    Integer{} -> tInteger
    Float{}   -> tFloat
    Char{}    -> tChar
    String{}  -> tString

inferOp :: OpF InferTExpr -> Infer (TypedExpr, [Assumption], [Constraint])
inferOp = \case
    AddS e1 e2 -> binOp AddS e1 e2 tInt tInt
    SubS e1 e2 -> binOp SubS e1 e2 tInt tInt
    MulS e1 e2 -> binOp MulS e1 e2 tInt tInt
    LtS e1 e2 -> binOp LtS e1 e2 tInt tBool
    GtS e1 e2 -> binOp GtS e1 e2 tInt tBool
    NegS e -> unOp NegS e tInt
    NotS e -> unOp NotS e tBool
    EqS e1 e2 -> do
        (_e1, t1, a1, c1) <- e1
        (_e2, t2, a2, c2) <- e2
        beta <- supply
        pure ( beta >*< OpS (EqS _e1 _e2)
             , a1 <> a2
             , c1 <> c2 <> [Equality t1 t2, Equality beta tBool] )

unOp
    :: (TExpr -> OpF TExpr)
    -> InferTExpr
    -> Type
    -> Infer (TypedExpr, [Assumption], [Constraint])
unOp op expr t = do
    (_e1, t1, a1, c1) <- expr
    beta <- supply
    pure ( beta >*< OpS (op _e1)
         , a1
         , c1 <> [Equality (TArr t1 beta) (TArr t t)] )

binOp
    :: (TExpr -> TExpr -> OpF TExpr)
    -> InferTExpr
    -> InferTExpr
    -> Type
    -> Type
    -> Infer (TypedExpr, [Assumption], [Constraint])
binOp op e1 e2 ta tb = do
    (_e1, t1, a1, c1) <- e1
    (_e2, t2, a2, c2) <- e2
    beta <- supply
    pure ( beta >*< OpS (op _e1 _e2)
         , a1 <> a2
         , c1 <> c2 <> [Equality (TArr t1 (TArr t2 beta)) (TArr ta (TArr ta tb))] )

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

(>*<) :: Type -> ExprF TExpr -> TypedExpr
t >*< a = TypedExpr $ Fix $ Const t :*: a

unfixt :: Infer (TypedExpr, [Assumption], [Constraint]) -> InferTExpr
unfixt expr = do
    (e, as, cs) <- first3 runTypedExpr <$> expr
    let Const t :*: _ = unfix e
    pure (e, t, as, cs)

{-# ANN inferOp ("HLint: ignore Reduce duplication" :: Text) #-}
