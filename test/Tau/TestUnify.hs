{-# LANGUAGE OverloadedStrings #-}
module Tau.TestUnify where

import Data.Text (Text, unpack)
import Tau.Type
import Tau.Type.Infer.Monad
import Tau.Type.Substitution
import Tau.Type.Unify
import Test.Hspec
import qualified Util.Pretty as Pretty

test010 :: (Type, Type)
test010 =
    ( TArr (TVar "a") (TVar "b")                     -- a -> b
    , TArr tInt tInt                                 -- Int -> Int
    )

test020 :: (Type, Type)
test020 =
    ( TArr (TVar "a") (TVar "a")                     -- a -> a
    , TArr tInt tBool                                -- Int -> Bool
    )

test030 :: (Type, Type)
test030 =
    ( TArr (TVar "a") (TVar "a")                     -- a -> a
    , TArr tInt tInt                                 -- Int -> Int
    )

test040 :: (Type, Type)
test040 =
    ( TArr (TVar "a") (TArr (TVar "b") (TVar "a"))   -- a -> (b -> a)
    , TArr (TVar "a") (TArr tInt (TVar "a"))         -- a -> (Int -> a)
    )

test041 :: (Type, Type)
test041 =
    ( TArr (TVar "a") (TArr (TVar "b") (TVar "a"))   -- a -> (b -> a)
    , TArr (TVar "a") (TArr tInt (TVar "b"))         -- a -> (Int -> b)
    )

test042 :: (Type, Type)
test042 =
    ( TArr (TVar "a") (TArr (TVar "b") (TVar "a"))   -- a -> (b -> a)
    , TArr tInt (TArr tInt tBool)                    -- Int -> (Int -> Bool)
    )

test050 :: (Type, Type)
test050 =
    ( TApp (TCon "List") (TVar "a")                  -- List a
    , TApp (TCon "List") tInt                        -- List Int
    )

test060 :: (Type, Type)
test060 =
    ( TApp (TCon "List") (TVar "a")                  -- List a
    , tInt                                           -- Int
    )

testUnify :: SpecWith ()
testUnify = do
    testSuccess test010 "test010"
    testFailure test020 "test020" 
    testSuccess test030 "test030"
    testSuccess test040 "test040"
    testSuccess test041 "test041"
    testFailure test042 "test042"
    testSuccess test050 "test050"
    testFailure test060 "test060"

shouldUnify :: (Type, Type) -> Expectation
shouldUnify (t1, t2) = 
    case runInfer (unify t1 t2) of
        Left{} ->
            expectationFailure "Unification failed"

        Right sub ->
            if apply sub t1 == apply sub t2 then
                pure ()

            else
                expectationFailure "Substitution does not yield equal types"

shouldFailToUnify :: (Type, Type) -> Expectation
shouldFailToUnify (t1, t2) =
    case runInfer (unify t1 t2) of
        Left{} ->
            pure ()

        Right{} ->
            expectationFailure "Expected unification to fail"

describeTest 
    :: ((Type, Type) -> Expectation) 
    -> String 
    -> (Type, Type) 
    -> Text 
    -> SpecWith ()
describeTest test outcome (t1, t2) name =
    describe (unpack description) $
        it outcome $ test (t1, t2)
  where
    description = 
        name <> ": The types (" 
             <> Pretty._type t1 
             <> ") and (" 
             <> Pretty._type t2 
             <> ")"

testSuccess, testFailure :: (Type, Type) -> Text -> SpecWith ()
testSuccess = describeTest shouldUnify "✔ should unify"
testFailure = describeTest shouldFailToUnify "✗ should not unify"
