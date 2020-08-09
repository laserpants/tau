{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Infer where

import Control.Monad.Except (throwError)
import Control.Monad.Reader (local, ask)
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Functor.Const
import Data.Functor.Foldable
import Data.Map.Strict (Map, notMember)
import Data.Text (Text)
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

infer :: Expr -> Infer (TypedExpr, [Assumption], [Constraint])
infer = cata $ \case
    VarS name -> do
        beta <- supply
        pure ( beta >*< VarS name
             , [(name, beta)]
             , [] )

    LamS name expr -> do
        beta@(TVar var) <- supply
        (t1, _expr, a1, c1) <- unfixt (local (insertIntoMonoset var) expr)
        pure ( TArr beta t1 >*< LamS name _expr
             , removeAssumption name a1
             , c1 <> [Equality t beta | (y, t) <- a1, name == y] )

    AppS exprs ->
        foldl1 inferApp exprs

    LitS prim -> do
        t <- inferPrim prim
        pure ( t >*< LitS prim, [], [] )

    LetS pairs body ->
        foldr inferLet body pairs

    IfS cond true false -> do
        (t1, _cond, a1, c1) <- unfixt cond
        (t2, _true, a2, c2) <- unfixt true
        (t3, _false, a3, c3) <- unfixt false
        pure ( t2 >*< IfS _cond _true _false
             , a1 <> a2 <> a3
             , c1 <> c2 <> c3 <> [Equality t1 tBool, Equality t2 t3] )

    CaseS _ [] ->
        throwError EmptyCaseStatement

    CaseS expr clss -> do
        beta <- supply
        (t1, _expr, a1, c1) <- unfixt expr
        (clss', as, cs) <- foldrM (inferClause beta t1) ([], [], []) clss
        pure ( beta >*< CaseS _expr clss'
             , a1 <> as
             , c1 <> cs )

    OpS op ->
        inferOp op

    AnnS expr ty ->
        undefined -- TODO

insertMany :: [Name] -> Monoset -> Monoset
insertMany = flip (foldr insertIntoMonoset)

getVars :: Pattern -> [Name]
getVars = cata alg where
    alg :: PatternF [Name] -> [Name]
    alg (VarP v)    = [v]
    alg (ConP _ ps) = concat ps
    alg _           = []

inferClause
    :: Type
    -> Type
    -> (Pattern, Infer (TypedExpr, [Assumption], [Constraint]))
    -> ([(Pattern, Fix (Const Type :*: ExprF))], [Assumption], [Constraint])
    -> Infer ([(Pattern, Fix (Const Type :*: ExprF))], [Assumption], [Constraint])
inferClause beta t (pttrn, expr) (ps, as, cs) = do
     (t1, _expr, a1, c1) <- unfixt (local (insertMany vars) expr)
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

inferApp
    :: Infer (TypedExpr, [Assumption], [Constraint])
    -> Infer (TypedExpr, [Assumption], [Constraint])
    -> Infer (TypedExpr, [Assumption], [Constraint])
inferApp fun arg = do
    (t1, _e1, a1, c1) <- unfixt fun
    (t2, _e2, a2, c2) <- unfixt arg
    beta <- supply
    pure ( beta >*< AppS [_e1, _e2]
         , a1 <> a2
         , c1 <> c2 <> [Equality t1 (TArr t2 beta)] )

inferPrim :: Prim -> Infer Type
inferPrim = \case
    Unit      -> pure tUnit
    Bool{}    -> pure tBool
    Int{}     -> pure tInt
    Integer{} -> pure tInteger
    Float{}   -> pure tFloat
    Char{}    -> pure tChar
    String{}  -> pure tString

inferLet
    :: (Name, Infer (TypedExpr, [Assumption], [Constraint]))
    -> Infer (TypedExpr, [Assumption], [Constraint])
    -> Infer (TypedExpr, [Assumption], [Constraint])
inferLet (var, expr) body = do
    (t1, _e1, a1, c1) <- unfixt expr
    (t2, _e2, a2, c2) <- unfixt body
    set <- ask
    pure ( t2 >*< LetS [(var, _e1)] _e2
         , removeAssumption var a1 <> removeAssumption var a2
         , c1 <> c2 <> [Implicit t t1 set | (y, t) <- a1 <> a2, var == y] )

inferOp
    :: OpF (Infer (TypedExpr, [Assumption], [Constraint]))
    -> Infer (TypedExpr, [Assumption], [Constraint])
inferOp = \case
     AddS e1 e2 -> binOp AddS e1 e2 tInt tInt
     SubS e1 e2 -> binOp SubS e1 e2 tInt tInt
     MulS e1 e2 -> binOp MulS e1 e2 tInt tInt
     LtS e1 e2 -> binOp LtS e1 e2 tInt tBool
     GtS e1 e2 -> binOp GtS e1 e2 tInt tBool
     NegS e -> unOp NegS e tInt
     NotS e -> unOp NotS e tBool
     EqS e1 e2 -> do
         (t1, _e1, a1, c1) <- unfixt e1
         (t2, _e2, a2, c2) <- unfixt e2
         beta <- supply
         pure ( beta >*< OpS (EqS _e1 _e2)
              , a1 <> a2
              , c1 <> c2 <> [Equality t1 t2, Equality beta tBool] )

unOp
    :: (Fix (Const Type :*: ExprF) -> OpF (Fix (Const Type :*: ExprF)))
    -> Infer (TypedExpr, [Assumption], [Constraint])
    -> Type
    -> Infer (TypedExpr, [Assumption], [Constraint])
unOp op expr t = do
    (t1, _e1, a1, c1) <- unfixt expr
    beta <- supply
    pure ( beta >*< OpS (op _e1)
         , a1
         , c1 <> [Equality (TArr t1 beta) (TArr t t)] )

binOp
    :: (Fix (Const Type :*: ExprF) -> Fix (Const Type :*: ExprF) -> OpF (Fix (Const Type :*: ExprF)))
    -> Infer (TypedExpr, [Assumption], [Constraint])
    -> Infer (TypedExpr, [Assumption], [Constraint])
    -> Type
    -> Type
    -> Infer (TypedExpr, [Assumption], [Constraint])
binOp op e1 e2 t0 t = do
    (t1, _e1, a1, c1) <- unfixt e1
    (t2, _e2, a2, c2) <- unfixt e2
    beta <- supply
    pure ( beta >*< OpS (op _e1 _e2)
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

(>*<) :: Type -> ExprF (Fix (Const Type :*: ExprF)) -> TypedExpr
t >*< a = TypedExpr $ Fix $ Const t :*: a

unfixt
    :: Infer (TypedExpr, [Assumption], [Constraint])
    -> Infer (Type, Fix TypedExprF, [Assumption], [Constraint])
unfixt expr = do
    (e, as, cs) <- first3 runTypedExpr <$> expr
    let Const t :*: _ = unfix e
    pure (t, e, as, cs)

{-# ANN inferOp ("HLint: ignore Reduce duplication" :: Text) #-}
