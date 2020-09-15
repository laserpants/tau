module Main where

import Control.Exception.Base

main = toTry `catch` handler

toTry = do
    print "hi"
    print (show (3 `div` 0))
    print "hi"

handler :: ArithException -> IO ()
handler DivideByZero = putStrLn "Divide by Zero!"
handler err = putStrLn "Some other error..."

--main :: IO ()
--main = pure ()
