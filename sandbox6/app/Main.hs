{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
module Main where

import Data.Aeson
import Data.Aeson.Encode.Pretty
import Data.Fix (Fix(..))
import Data.Function (fix)
import Data.Functor.Foldable
import Data.Text (pack)
import Stuff
import System.Environment
import Tau.Serializers
import Tau.Util (Coalgebra)
import qualified Data.ByteString.Lazy.Char8 as B


data Stream = Stream
    { _head :: Int 
    , _tail :: Stream 
    } deriving (Show, Eq)


implFun :: (a -> s -> (a, s)) -> a -> s
implFun f n = let (m, s) = f n (implFun f m) in s

clientFun :: Int -> Stream -> (Int, Stream)
clientFun n next = (n + 1, Stream { _head = n, _tail = next })


go = implFun clientFun 1

foo = _head go


--data StreamF a = StreamF
--    { _head :: Int 
--    , _tail :: StreamF a }
--    deriving (Show, Eq, Functor)
--
--type Stream = Fix StreamF
--
---- para - apo
--
--build :: Int -> Stream
--build n = apo go n where
--  go :: Int -> StreamF (Either Stream Int)
----  go 0 = StreamF { _head = 1, _tail = StreamF { _head = 1, _tail = undefined } }
--  go n = StreamF { _head = 1, _tail = undefined }



main :: IO ()
main = do
    [p] <- getArgs
    

    -- (False.foo)({ foo = ... })

    -- (foo(False))({ foo = ... })

    -- (foo(False, { foo = ... })

    --let p = "{ foo = () => true }.foo(false)"
--    let p = "{ foo = () => true }.foo()"

--    let p = "{ foo = _ => \"Hello\" }.foo(0)"

--    let p = "let g = (x : int) => x + 3 in let f = (x : int) => x + 1 in 5.f.g"

--    let p = "{ foo = x => \"Hello\" }.foo(false)"

    -- B.putStrLn (encodePretty' defConfig{ confIndent = Spaces 2 } (toRep (runBundle (pack p))))
--    let p = "let f(x) = x > 3 in f(3 : int)"
    B.putStrLn (encode (toRep (runBundle (pack p))))


--let f(x) = x + 1 > 5 in f(5)

--let foo 
--  | 0 => 1 
--  | n => 2
--  in foo(1)


-- let
--   foo(x) =
--     x > 5
--   in 
--     foo(8)
--

-- let f(x) = x + 1 in f(123)

-- let f(x) = x + 1 in f(123 : int)
--
--
-- let f(x) = 11 in x => show(read(x))
--
