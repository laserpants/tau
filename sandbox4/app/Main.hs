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
                [ Clause [litPat () (LInt 5)] [] (varExpr () "1")
                , Clause [varPat () "y"] [] (varExpr () "2") ])
        , litExpr () (LInt 5) ]


test22 = case test2 of
    Just c -> 
        evalExpr c mempty

--test1 = runSupply e (numSupply "$")
--  where
--    e :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
--    e = pipeline mapPairs

main = print "Hello"
