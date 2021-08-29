module Main where

import Data.Aeson
import Data.Aeson.Encode.Pretty
import Data.Text (pack)
import Stuff
import System.Environment
import Tau.Serializers
import qualified Data.ByteString.Lazy.Char8 as B

main :: IO ()
main = do
    [p] <- getArgs
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
