{-# LANGUAGE LambdaCase #-}
module Tau.Type.Unify where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS.Strict
import Control.Monad.State
import Data.Map (Map)
import Data.Set (difference, member)
import Tau.Core (Expr(..), Value(..), Op(..))
import Tau.Type (Type(..), Scheme(..), Constraint(..), Free(..), Substitutable(..), Sub, compose, emptySub, substitute, tyBool, tyInt, tyString, tyChar, tyUnit)
import Tau.Type.Context (Context(..), extend, remove)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Tau.Type.Context as Context


type Infer = RWST Context (List Constraint) Int (Except String)


type Solve = Except String


instantiate :: Scheme -> Infer Type
instantiate (Forall vars tau) = do
    vars' <- mapM (const fresh) varsL
    pure $ apply (Map.fromList (varsL `zip` vars')) tau
  where
    varsL = Set.toList vars


generalize :: Context -> Type -> Scheme
generalize context tau =
    Forall (free tau `difference` free context) tau


unify :: Type -> Type -> Infer ()
unify t1 t2 = tell [Constraint t1 t2]


inferConstraints :: Expr -> Infer ( Type, List Constraint )
inferConstraints expr = do
    state <- get
    context <- ask
--    liftEither (runExcept (evalRWST (infer expr) context state))
    case runExcept (runRWST (infer expr) context state) of
        Left err ->
            throwError err

        Right ( t, s, cs ) ->
            put s >> pure ( t, cs )


infer :: Expr -> Infer Type
infer = \case

    Lit (Int _) ->
        pure tyInt

    Lit (Bool _) ->
        pure tyBool

    Lit (String _) ->
        pure tyString

    Lit (Char _) ->
        pure tyChar

    Lit Unit ->
        pure tyUnit

    Var name -> do
        Context env <- ask
        case Map.lookup name env of
            Nothing ->
                throwError ("Unbound variable `" ++ Text.unpack name ++ "`.")

            Just scheme ->
                instantiate scheme

    Lam name body -> do
        t1 <- fresh
        t2 <- local (extend name (Forall Set.empty t1)) (infer body)
        pure (TyArr t1 t2)

    App fun arg -> do
        t1 <- infer fun
        t2 <- infer arg
        t3 <- fresh
        unify t1 (TyArr t2 t3)
        pure t3

    Let name expr body -> do
        context <- ask
        ( t1, constraints ) <- inferConstraints (Fix (Lam name expr))
        sub <- lift (solve constraints)
        let scheme = generalize (apply sub context) (apply sub t1)
        local (apply sub . extend name scheme) (infer body)

    If cond true false -> do
        t1 <- infer cond
        t2 <- infer true
        t3 <- infer false
        unify t1 tyBool
        unify t2 t3
        pure t2

    Fix expr -> do
        t1 <- infer expr
        t2 <- fresh
        unify (TyArr t2 t2) t1
        pure t2

    Op op a b -> do
        t1 <- infer a
        t2 <- infer b
        t3 <- fresh
        unify (TyArr t1 (TyArr t2 t3)) (ops op)
        pure t3

    Neg a ->
        pure tyInt


ops :: Op -> Type
ops = \case

    Add ->
        tyInt `TyArr` (tyInt `TyArr` tyInt)

    Sub ->
        tyInt `TyArr` (tyInt `TyArr` tyInt)

    Mul ->
        tyInt `TyArr` (tyInt `TyArr` tyInt)

    Eq ->
        tyInt `TyArr` (tyInt `TyArr` tyBool)


fresh :: Infer Type
fresh = do
    count <- get
    modify (+1)
    pure $ TyVar (letters !! count)


letters = fmap Text.pack ( [1..] >>= flip replicateM ['a'..'z'] )


runInfer :: Infer a -> Either String ( a, List Constraint )
runInfer stack =
    runExcept (evalRWST stack Context.empty 0)


occursIn :: Free a => Name -> a -> Bool
occursIn name = member name . free


unifies :: Type -> Type -> Solve Sub
unifies = curry $ \case

    ( TyCon a, TyCon b )
        | a == b -> pure emptySub

    ( TyArr a b, TyArr a1 b1 ) -> do
        t1 <- unifies a a1
        t2 <- unifies (apply t1 b) (apply t1 b1)
        pure (t2 `compose` t1)

    ( TyVar a, TyVar b )
        | a == b -> pure emptySub

    ( TyVar name, tau )
        | name `occursIn` tau -> throwError "Cannot construct infinite type."
        | otherwise           -> pure (substitute name tau)

    ( tau, TyVar name ) ->
        unifies (TyVar name) tau

    _ ->
        throwError "Unification failed."


solve :: List Constraint -> Solve Sub
solve =
    foldM go emptySub
  where
    go sub (Constraint t1 t2) = do
        sub1 <- unifies (apply sub t1) (apply sub t2)
        --pure (sub `compose` sub1)
        pure (sub1 `compose` sub)


runSolver :: List Constraint -> Either String Sub
runSolver constraints =
    runExcept (solve constraints)
