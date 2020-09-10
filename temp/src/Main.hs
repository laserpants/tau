{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Except
import Control.Monad.Supply
import Debug.Trace
import Tau.Juice
import Tau.Solver
import Tau.Expr
import Tau.Type
import Tau.Util

main :: IO ()
main = pure ()

cs1 :: [TypeConstraint]
cs1 = 
    [ -- Implicit (varT "a2") (varT "a1") (Monoset mempty)
--    , Explicit (varT "a1") (forall ["a"] [TyCl "Num" (VarT "a")] (ArrT (VarT "a") (ArrT (VarT "a") (VarT "a"))))
    ]

runSolver :: IO (Either (TypeError UnificationError) (Substitution Type, [TyClass]))
runSolver = evalSupplyT (runExceptT (solveTypes cs1)) (nameSupply "$$a")
