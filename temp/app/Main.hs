{-# LANGUAGE OverloadedStrings #-}
module Main where

--import Debug.Trace
--import Tau.Expr
import Control.Monad.Except
import Control.Monad.Supply
import Tau.Solver
import Tau.Type
import Tau.Parser
import Tau.Util

main :: IO ()
main = pure ()

cs1 :: [TypeConstraint]
cs1 = 
    [ Implicit (varT "a2") (varT "a1") (Monoset mempty)
    , Explicit (varT "a1") (Forall ["a"] [TyCl "Num" (varT "a")] (arrT (varT "a") (arrT (varT "a") (varT "a"))))
    ]

runSolver :: IO (Either TypeError (Substitution Type, [TyClass]))
runSolver = evalSupplyT (runExceptT (solveTypes cs1)) (nameSupply "$$a")
