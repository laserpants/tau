{-# LANGUAGE StrictData #-}
module Foo where

data R = R { _head :: () -> Int, _tail :: () -> R }

myFun :: Int -> (Int -> R) -> R 
myFun n next =
    R { _head = \_ -> n, _tail = \_ -> next (n + 1) }

---unfoldx :: (a -> (a -> b) -> (a, b)) -> a -> b
unfoldx f n =
    f n (unfoldx f)

testRun = _head (_tail (unfoldx myFun 1) ()) ()
