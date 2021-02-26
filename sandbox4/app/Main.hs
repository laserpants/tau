{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Supply 
import Data.Maybe
import Data.Text (Text)
import Tau.Comp.Core
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import qualified Tau.Util.Env as Env

noDups = undefined

mapPairs :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs =
    matchAlgo
        [varExpr () "u1", varExpr () "u2", varExpr () "u3"] 
        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "e1")
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (varExpr () "e2")
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
        ]
        (varExpr () "FAIL")

mapPairs2 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs2 =
    matchAlgo
        [varExpr () "u2", varExpr () "u3"] [ Clause [conPat () "[]" [], varPat () "ys"] [] (varExpr () "e1")
        , Clause [conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (varExpr () "e2")
        , Clause [conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
        ]
        (varExpr () "FAIL")

mapPairs3 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs3 =
    matchAlgo
        [varExpr () "u2"] 
        [ Clause [conPat () "[]" []] [] (varExpr () "e1")
--        , Clause [varPat () "x", varPat () "xs", conPat () "[]" []] [] (varExpr () "e2")
--        , Clause [varPat () "x", varPat () "xs", conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
        ]
        (varExpr () "FAIL")


mapPairs4 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs4 =
    matchAlgo
        [] 
        [ Clause [] [] (varExpr () "e2")
        ]
        (varExpr () "FAIL")



test1 = evalSupply mapPairs (numSupply "$")


test2 = evalSupply (pipeline e) (numSupply "$")
  where
    e = appExpr ()
            [ lamExpr () [varPat () "x"]
                (patExpr () [varExpr () "x"]
                    [ Clause [litPat () (LInt 5)] [] (litExpr () (LInt 1))
                    , Clause [varPat () "y"] [] (litExpr () (LInt 2)) ])
            , litExpr () (LInt 5) ]

test22 = case test2 of
    Just c -> do
        traceShowM c
        evalExpr c mempty

test3 = evalSupply (pipeline e) (numSupply "$")
  where 
    e = patExpr () [litExpr () (LInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (LInt 9), conExpr () "[]" []]]
        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "ys")
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (litExpr () (LString "e2"))
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (litExpr () (LString "e3"))
        ]

test33 = case test3 of
    Just c -> do
        traceShowM c
        evalExpr c evalEnv

evalEnv = Env.fromList 
    [ ("(::)" , constructor "(::)" 2)  
    , ("[]"   , constructor "[]"   0)  
    ]
 

-- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
test4 = evalSupply (pipeline e) (numSupply "$")
  where 
    e = letExpr () (BLet (varPat () "f")) (patExpr () [] 
        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
      ]) (appExpr () [varExpr () "f", litExpr () (LInt 5)]) 

--    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]])

test44 = case test4 of
    Just c -> do
        traceShowM c
        evalExpr c evalEnv


-- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
test5 = evalSupply (pipeline e) (numSupply "$")
  where 
    e = fixExpr () "f" (patExpr () [] 
        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
      ]) (appExpr () [varExpr () "f", litExpr () (LInt 10)]) 

--    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]])

test55 = case test5 of
    Just c -> do
        traceShowM c
        evalExpr c evalEnv




--test1 = runSupply e (numSupply "$")
--  where
--    e :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
--    e = pipeline mapPairs

main = print "Hello"
