{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Tau.Type.Unify where

import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.RWS.Strict
import Data.Map (Map)
import Data.Set (difference, member)
import Tau.Core (Expr(..), Value(..), Op(..))
import Tau.Type (Type(..), Scheme(..), Constraint(..), Free(..), Substitutable(..), Sub, compose, emptySub, substitute)
import Tau.Type (apply)
import Tau.Type.Context (Context(..), extend, remove)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Tau.Type.Context as Context

import Debug.Trace


type Infer = RWST Context [Constraint] Int (Either String)


type Solve = Either String


instantiate :: Scheme -> Infer Type
instantiate (Forall vars tau) = do
--    trace (show (Forall vars tau)) $ do
    vars' <- mapM (const fresh) varsL
    pure $ apply (Map.fromList (varsL `zip` vars')) tau
  where
    varsL = Set.toList vars


generalize :: Context -> Type -> Scheme
generalize context tau =
    Forall (free tau `difference` free context) tau


inContext :: Var -> Scheme -> Infer a -> Infer a
inContext name scheme = do
    local (extend name scheme . remove name)


infer :: Expr -> Infer Type
infer = \case
    Var name -> do
        Context env <- ask
--        trace (show name) $
        case Map.lookup name env of
            Nothing ->
                lift (Left "Unbound variable")

            Just scheme -> do
                trace (show scheme) $ pure ()
                instantiate scheme

    Lit (Int _) ->
        pure TyInt

    Lit (Bool _) ->
        pure TyBool

    Lam name body -> do
        t1 <- fresh
        t2 <- inContext name (Forall Set.empty t1) (infer body)
        pure (TyArr t1 t2)

    App fun arg -> do
        t1 <- infer fun
        t2 <- infer arg 
        t3 <- fresh
        unify t1 (TyArr t2 t3)
        pure t3

    Let name expr body -> do
        context <- ask
        t1 <- infer expr
        
        t2 <- inContext name (generalize context t1) (infer body)
        ----let (RWST a) = inContext name (generalize context t1) (infer body)
        ----trace (show a) $ pure ()
        pure t2

        -- Int -> Int -> a  ~  Int -> Int -> Int

    If cond true false -> do
        t1 <- infer cond
        t2 <- infer true
        t3 <- infer false
        unify t1 TyBool
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
        let u1 = TyArr t1 (TyArr t2 t3)
        let u2 = (Map.!) ops op
        unify u1 u2
        pure t3


ops :: Map Op Type
ops = Map.fromList 
    [ ( Add, (TyInt `TyArr` (TyInt `TyArr` TyInt)) )
    , ( Mul, (TyInt `TyArr` (TyInt `TyArr` TyInt)) )
    , ( Sub, (TyInt `TyArr` (TyInt `TyArr` TyInt)) )
    , ( Eq, (TyInt `TyArr` (TyInt `TyArr` TyBool)) )
    ]


unify :: Type -> Type -> Infer ()
unify t1 t2 = tell [Constraint t1 t2]


fresh :: Infer Type
fresh = do
    count <- get
    modify (+1)
    pure $ TyVar (letters !! count)


letters = fmap Text.pack ( [1..] >>= flip replicateM ['a'..'z'] )


runInfer :: Infer Type -> Either String ( Type, [Constraint] )
runInfer state =
    evalRWST state Context.empty 0


unifies :: Type -> Type -> Solve Sub
unifies = curry $ \case

    ( TyBool, TyBool ) -> 
        pure emptySub

    ( TyInt, TyInt ) -> 
        pure emptySub

    ( TyArr a b, TyArr a1 b1 ) -> do
        t1 <- unifies a a1
        t2 <- unifies (apply t1 b) (apply t1 b1)
        pure (t2 `compose` t1)

    ( TyVar a, TyVar b ) 
        | a == b -> pure emptySub

    ( TyVar name, tau ) 
        | name `occursIn` tau -> Left "Infinite type"
        | otherwise           -> pure (substitute name tau)

    ( tau, TyVar name ) -> 
        unifies (TyVar name) tau

    _ -> 
        Left "Unification failed"

  where
    occursIn name = member name . free


solve :: ( Sub, [Constraint] ) -> Solve Sub
solve ( sub, constraints ) =
    foldM go emptySub constraints
  where
    go :: Sub -> Constraint -> Solve Sub
    go sub (Constraint t1 t2) = do
        sub1 <- unifies (apply sub t1) (apply sub t2)
        pure (sub `compose` sub1)


runSolver :: [Constraint] -> Either String Sub
runSolver constraints =
    solve ( Map.empty, constraints )
