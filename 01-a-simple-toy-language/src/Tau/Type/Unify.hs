{-# LANGUAGE LambdaCase #-}
module Tau.Type.Unify where

import Control.Monad.Except
import Control.Monad.Reader
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


type Infer a = ExceptT String (ReaderT Context (State Int)) a


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


inContext :: Name -> Scheme -> Infer a -> Infer a
inContext name scheme =
    local (extend name scheme . remove name)


infer :: Expr -> Infer ( Type, List Constraint )
infer = \case

    Lit (Int _) ->
        pure ( tyInt, [] )

    Lit (Bool _) ->
        pure ( tyBool, [] )

    Lit (String _) ->
        pure ( tyString, [] )

    Lit (Char _) ->
        pure ( tyChar, [] )

    Lit Unit ->
        pure ( tyUnit, [] )

    Var name -> do
        Context env <- ask
        case Map.lookup name env of
            Nothing ->
                throwError ("Unbound variable `" ++ Text.unpack name ++ "`.")

            Just scheme -> do
                t <- instantiate scheme
                pure ( t, [] )

    Lam name body -> do
        t1 <- fresh
        ( t2, c2 ) <- inContext name (Forall Set.empty t1) (infer body)
        pure ( TyArr t1 t2, c2 )

    App fun arg -> do
        ( t1, c1 ) <- infer fun
        ( t2, c2 ) <- infer arg
        t3 <- fresh
        pure ( t3, c1 ++ c2 ++ [Constraint t1 (TyArr t2 t3)] )

    Let name expr body -> do
        context <- ask
        ( t1, c1 ) <- infer (Fix (Lam name expr))
        case runSolver c1 of
            Left err -> 
                throwError err

            Right sub -> do
                let sc = generalize (apply sub context) (apply sub t1)
                ( t2, c2 ) <- inContext name sc (local (apply sub) (infer body))
                pure (t2, c1 ++ c2)

    If cond true false -> do
        ( t1, c1 ) <- infer cond
        ( t2, c2 ) <- infer true
        ( t3, c3 ) <- infer false
        pure ( t2, c1 ++ c2 ++ c3 ++ [Constraint t1 tyBool, Constraint t2 t3] )

    Fix expr -> do
        ( t1, c1 ) <- infer expr
        t2 <- fresh
        pure ( t2, c1 ++ [Constraint (TyArr t2 t2) t1] )

    Op op a b -> do
        ( t1, c1 ) <- infer a
        ( t2, c2 ) <- infer b
        t3 <- fresh
        let u1 = TyArr t1 (TyArr t2 t3)
            u2 = (Map.!) ops op
        pure ( t3, c1 ++ c2 ++ [Constraint u1 u2] )


ops :: Map Op Type
ops = Map.fromList 
    [ ( Add, (tyInt `TyArr` (tyInt `TyArr` tyInt)) )
    , ( Mul, (tyInt `TyArr` (tyInt `TyArr` tyInt)) )
    , ( Sub, (tyInt `TyArr` (tyInt `TyArr` tyInt)) )
    , ( Eq, (tyInt `TyArr` (tyInt `TyArr` tyBool)) )
    ]


fresh :: Infer Type
fresh = do
    count <- get
    modify (+1)
    pure $ TyVar (letters !! count)


letters = fmap Text.pack ( [1..] >>= flip replicateM ['a'..'z'] )


runInfer :: Infer a -> Either String a
runInfer reader =
    evalState (runReaderT (runExceptT reader) Context.empty) 0


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
        | name `occursIn` tau -> throwError "Infinite type"
        | otherwise           -> pure (substitute name tau)

    ( tau, TyVar name ) -> 
        unifies (TyVar name) tau

    _ -> 
        throwError "Unification failed"


solve :: ( Sub, List Constraint ) -> Solve Sub
solve ( sub, constraints ) =
    foldM go emptySub constraints
  where
    go sub (Constraint t1 t2) = do
        sub1 <- unifies (apply sub t1) (apply sub t2)
        pure (sub `compose` sub1)


runSolver :: List Constraint -> Either String Sub
runSolver constraints =
    runExcept (solve ( Map.empty, constraints ))
