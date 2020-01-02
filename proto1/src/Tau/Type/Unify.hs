{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Tau.Type.Unify where

import Control.Monad.State
import Control.Monad.RWS.Strict
import Data.Map (Map)
import Data.Set (difference, member)
import Tau.Core (Expr(..), Value(..), Op(..))
import Tau.Type (Type(..), Scheme(..), Free(..), Sub, compose, singleSub)
import Tau.Type (substitute)
import Tau.Type.Context (Context(..), extend, remove)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Tau.Type.Context as Context


data UniState = UniState
    { count :: Int
    } deriving (Show, Eq, Ord)


newUniState :: UniState
newUniState = UniState { count = 0 }


type Constraint = ( Type, Type )


type Unify = RWST Context [Constraint] UniState (Either String)


counterStep :: Unify Int
counterStep = do
    UniState{ count = count, .. } <- get
    put UniState{ count = count + 1, .. }
    pure count


instantiate :: Scheme -> Unify Type
instantiate (Forall vars tau) = do
    vars' <- mapM (const fresh) varsL
    pure $ substitute (Map.fromList (varsL `zip` vars')) tau
  where
    varsL = Set.toList vars


generalize :: Context -> Type -> Scheme
generalize context tau =
    Forall (free tau `difference` free context) tau


inContext :: Var -> Scheme -> Unify a -> Unify a
inContext name scheme =
    local (extend name scheme . remove name)


infer :: Expr -> Unify Type
infer = \case
    Var name -> do
        Context env <- ask
        case Map.lookup name env of
            Nothing ->
                fail "Unbound variable"

            Just scheme -> do
                instantiate scheme

        --case Map.lookup name env of
        --    Nothing ->
        --        fail "Unbound variable"

        --    Just scheme -> do
        --        t1 <- instantiate scheme
        --        pure ( mempty, t1 )

    Lit (Int _) ->
        pure TInt
        --pure ( mempty, TInt )

    Lit (Bool _) ->
        pure TBool
        --pure ( mempty, TBool )

    Lam name body -> do
        t1 <- fresh
        t2 <- inContext name (Forall Set.empty t1) (infer body)
        pure (TArr t1 t2)
        --t <- fresh
        --let env' = extend name (Forall mempty t) context
        --( s1, t1 ) <- infer env' body
        --pure ( s1, TArr (substitute s1 t) t1 )

    App fun arg -> do
        t1 <- infer fun
        t2 <- infer arg
        t3 <- fresh
        unify t1 (TArr t2 t3)   -- ?
        pure t3
        --t <- fresh
        --( s1, t1 ) <- infer context fun
        --( s2, t2 ) <- infer (Context.substitute s1 context) arg
        --s3 <- unify (substitute s2 t1) (TArr t2 t)
        --pure ( s3 `compose` s2 `compose` s1, substitute s3 t )

    Let name expr body -> do
        context <- ask
        t1 <- infer expr
        inContext name (generalize context t1) (infer body)
        --( s1, t1 ) <- infer context expr
        --let env' = Context.substitute s1 context
        --    t'   = generalize env' t1
        --( s2, t2 ) <- infer (extend name t' env') body
        --pure ( s1 `compose` s2, t2 )

    If cond true false -> do
        t1 <- infer cond
        t2 <- infer true
        t3 <- infer false
        unify t1 TBool
        unify t2 t3
        pure t2
        --( s1, t1 ) <- infer context cond
        --( s2, t2 ) <- infer context true
        --( s3, t3 ) <- infer context false
        --s4 <- unify t1 TBool
        --s5 <- unify t2 t3
        --pure ( s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, substitute s5 t2 )

    Fix expr -> do
        t1 <- infer expr
        t2 <- fresh
        unify (TArr t2 t2) t1
        pure t2
        --( s1, t1 ) <- infer context expr
        --t <- fresh
        --s2 <- unify (TArr t t) t1
        --pure ( s2, substitute s1 t )

    Op op a b -> do
        t1 <- infer a
        t2 <- infer b
        t3 <- fresh
        let u1 = TArr t1 (TArr t2 t3)
        let u2 = ops Map.! op
        unify u1 u2
        pure t3
        --( s1, t1 ) <- infer context a
        --( s2, t2 ) <- infer context b
        --t <- fresh
        --s3 <- unify (TArr t1 (TArr t2 t)) (ops Map.! op)
        --pure ( s1 `compose` s2 `compose` s3, substitute s3 t )


ops :: Map Op Type
ops = Map.fromList 
    [ ( Add, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Mul, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Sub, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Eq, (TInt `TArr` (TInt `TArr` TBool)) )
    ]


-- http://www.macs.hw.ac.uk/~yl55/UnPublished/ThesisMainText.pdf
--
unify :: Type -> Type -> Unify ()
unify t1 t2 = tell [( t1, t2 )]

--unify = curry $ \case 
--    ( TBool, TBool ) -> 
--        pure mempty
--
--    ( TInt, TInt ) -> 
--        pure mempty
--
--    ( a `TArr` b, a1 `TArr` b1 ) -> do
--        t1 <- unify a a1
--        t2 <- unify (substitute t1 b) (substitute t1 b1)
--        pure (t2 `compose` t1)
--
--    ( TVar a, TVar b ) 
--        | a == b -> pure mempty
--
--    ( TVar name, tau ) 
--        | name `occursIn` tau -> fail "Infinite type"
--        | otherwise           -> pure (singleSub name tau)
--
--    ( tau, TVar name ) -> 
--        unify (TVar name) tau
--
--    _ -> 
--        fail "Unification failed"
--
--  where
--    occursIn name = member name . free


fresh :: Unify Type
fresh = do
    count <- counterStep
    let var = letters !! count
    pure (TVar var)


letters = fmap Text.pack ( [1..] >>= flip replicateM ['a'..'z'] )


runInfer :: Unify a -> Either String ( a, [Constraint] )
runInfer state =
    evalRWST state Context.empty newUniState
