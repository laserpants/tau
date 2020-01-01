{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Tau.Type.Unify where

import Control.Monad.State
import Data.Map (Map)
import Data.Set (difference, member)
import Tau.Parts
import Tau.Syntax (Expr(..), Value(..), Op(..))
import Tau.Type (Type(..), Scheme(..), Free(..), Sub)
import Tau.Type (apply)
import Tau.Type.Context (Context(..), extend)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Tau.Type.Context as Context


data UniState = UniState
    { count :: Int
    } deriving (Show, Eq, Ord)


newUniState :: UniState
newUniState = UniState { count = 0 }


counterStep :: State UniState Int
counterStep = do
    UniState{ count = count, .. } <- get
    put UniState{ count = count + 1, .. }
    pure count


type Unify = State UniState


instantiate :: Scheme -> Unify Type
instantiate (Forall vars tau) = do
    vars' <- mapM (const fresh) varsL
    pure $ apply (Map.fromList (varsL `zip` vars')) tau
  where
    varsL = Set.toList vars


generalize :: Context -> Type -> Scheme
generalize context tau =
    Forall (free tau `difference` free context) tau


substitute :: Var -> Type -> Sub
substitute = Map.singleton


compose :: Sub -> Sub -> Sub
compose sub1 sub2 = 
    Map.map (apply sub1) sub2 `Map.union` sub1


infer :: Context -> Expr -> Unify ( Sub, Type )
infer context = \case
    Var name -> 
        let 
            Context env = context
        in
        case Map.lookup name env of
            Nothing ->
                fail "Unbound variable"

            Just scheme -> do
                t1 <- instantiate scheme
                pure ( mempty, t1 )

    Lit (Int _) ->
        pure ( mempty, TInt )

    Lit (Bool _) ->
        pure ( mempty, TBool )

    Lam name body -> do
        t <- fresh
        let env' = extend name (Forall mempty t) context
        ( s1, t1 ) <- infer env' body
        pure ( s1, TArr (apply s1 t) t1 )

    App fun arg -> do
        t <- fresh
        ( s1, t1 ) <- infer context fun
        ( s2, t2 ) <- infer (Context.apply s1 context) arg
        s3 <- unify (apply s2 t1) (TArr t2 t)
        pure ( s3 `compose` s2 `compose` s1, apply s3 t )

    Let name expr body -> do
        ( s1, t1 ) <- infer context expr
        let env' = Context.apply s1 context
            t'   = generalize env' t1
        ( s2, t2 ) <- infer (extend name t' env') body
        pure ( s1 `compose` s2, t2 )

    If cond true false -> do
        ( s1, t1 ) <- infer context cond
        ( s2, t2 ) <- infer context true
        ( s3, t3 ) <- infer context false
        s4 <- unify t1 TBool
        s5 <- unify t2 t3
        pure ( s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, apply s5 t2 )

    Fix expr -> do
        ( s1, t1 ) <- infer context expr
        t <- fresh
        s2 <- unify (TArr t t) t1
        pure ( s2, apply s1 t )

    Op op a b -> do
        ( s1, t1 ) <- infer context a
        ( s2, t2 ) <- infer context b
        t <- fresh
        s3 <- unify (TArr t1 (TArr t2 t)) (ops Map.! op)
        pure ( s1 `compose` s2 `compose` s3, apply s3 t )


ops :: Map Op Type
ops = Map.fromList 
    [ ( Add, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Mul, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Sub, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Eq, (TInt `TArr` (TInt `TArr` TBool)) )
    ]


-- http://www.macs.hw.ac.uk/~yl55/UnPublished/ThesisMainText.pdf
--
unify :: Type -> Type -> Unify Sub
unify = curry $ \case 
    ( TBool, TBool ) -> 
        pure mempty

    ( TInt, TInt ) -> 
        pure mempty

    ( a `TArr` b, a1 `TArr` b1 ) -> do
        t1 <- unify a a1
        t2 <- unify (apply t1 b) (apply t1 b1)
        pure (t2 `compose` t1)

    ( TVar a, TVar b ) 
        | a == b -> pure mempty

    ( tau, TVar name ) -> 
        unify (TVar name) tau

    ( TVar name, tau ) 
        | name `occursIn` tau -> fail "Infinite type"
        | otherwise           -> pure (substitute name tau)

    _ -> 
        fail "Unification failed"

  where
    occursIn name = member name . free


fresh :: Unify Type
fresh = do
    count <- counterStep
    let var = letters !! count
    pure (TVar var)


letters = fmap Text.pack ( [1..] >>= flip replicateM ['a'..'z'] )


runInfer :: Unify a -> a
runInfer state =
    evalState state newUniState 
