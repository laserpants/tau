{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE StrictData    #-}
{-# LANGUAGE TypeOperators #-}
module Tau.Type.Infer where

import Control.Arrow ((>>>))
import Control.Monad.Except (throwError)
import Control.Monad.Reader (local, ask)
import Control.Monad.Supply
import Data.Functor.Const
import Data.Functor.Foldable
import Data.Map.Strict (Map, notMember)
import Data.Tuple.Extra (fst3, first3)
import Tau.Ast
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
            <*> (expr |> fmap fmap fmap (first3 getType) |> inferAlg)

inferAlg 
    :: ExprF (Infer (Type, [Assumption], [Constraint])) 
    -> Infer (Type, [Assumption], [Constraint])
inferAlg = \case
    VarS name -> do
        beta <- supply
        pure (beta, [(name, beta)], [])

    LamS name expr -> do
        beta@(TVar var) <- supply
        (t1, a1, c1) <- local (insertIntoMonoset var) expr
        pure ( TArr beta t1
             , removeAssumption name a1
             , c1 <> [Equality t beta | (y, t) <- a1, var == y] )

    AppS exprs ->
        foldl1 inferApp exprs

    LitS Unit      -> pure (tUnit, [], [])
    LitS Bool{}    -> pure (tBool, [], [])
    LitS Int{}     -> pure (tInt, [], [])
    LitS Integer{} -> pure (tInteger, [], [])
    LitS Float{}   -> pure (tFloat, [], [])
    LitS Char{}    -> pure (tChar, [], [])
    LitS String{}  -> pure (tString, [], [])

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
        undefined

    OpS op ->
        inferOp op

    AnnS expr ty -> do
        (t1, a1, c1) <- expr
        undefined

inferApp 
    :: Infer (Type, [Assumption], [Constraint])
    -> Infer (Type, [Assumption], [Constraint])
    -> Infer (Type, [Assumption], [Constraint])
inferApp fun arg = do
    (t1, a1, c1) <- fun
    (t2, a2, c2) <- arg
    beta <- supply
    pure ( beta
         , a1 <> a2
         , c1 <> c2 <> [Equality t1 (TArr t2 beta)] )

inferLet
    :: (Name, Infer (Type, [Assumption], [Constraint]))
    -> Infer (Type, [Assumption], [Constraint])
    -> Infer (Type, [Assumption], [Constraint])
inferLet (var, expr) body = do
    (t1, a1, c1) <- expr
    (t2, a2, c2) <- body
    set <- ask
    pure ( t2
         , removeAssumption var a1 <> removeAssumption var a2
         , c1 <> c2 <> [Implicit t t1 set | (y, t) <- a1 <> a2, var == y] )

inferOp :: OpF a -> Infer (Type, [Assumption], [Constraint])
inferOp = \case
    AddS a b ->
        undefined
    SubS a b ->
        undefined
    MulS a b ->
        undefined
    EqS a b ->
        undefined
    LtS a b ->
        undefined
    GtS a b ->
        undefined
    NegS a ->
        undefined
    NotS a ->
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
