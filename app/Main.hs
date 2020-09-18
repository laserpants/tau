{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Exception.Base
import qualified Tau.Env.Builtin as Builtin
import qualified Tau.Util.TH
import Tau.Type.Inference
import Tau.Type

xxx = runInferType Builtin.typeSchemes $(Tau.Util.TH.parseExpr "let plus1 = 'x' in let x = let plus1 = \\n => n + 1 in 4.plus1 in plus1")

--kmain = toTry `catch` handler
--k
--ktoTry = do
--k    print "hi"
--k    print (show (3 `div` 0))
--k    print "hi"
--k
--khandler :: ArithException -> IO ()
--khandler DivideByZero = putStrLn "Divide by Zero!"
--khandler err = putStrLn "Some other error..."

main :: IO ()
main = pure ()
