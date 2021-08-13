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
    B.putStrLn (encodePretty' defConfig{ confIndent = Spaces 2 } (toRep (runBundle (pack p))))
