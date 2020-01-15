{-# LANGUAGE OverloadedStrings #-}
module Tau.Repl where

import Control.Monad.Reader
import Control.Monad.Trans
import Data.List (isPrefixOf)
import Data.Text (Text, pack)
import System.Console.Repline
import Tau.Core
import Tau.Core.Parser
import Tau.Eval
import Tau.Type
import Tau.Type.Context (Context(..))
import Tau.Type.Unify
import Tau.Util
import Text.Megaparsec
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Tau.Util.Print as Print


type Repl a = HaskelineT IO a


eval_ :: Expr -> Value
eval_ expr = runReader (eval expr) mempty


cmd :: String -> Repl ()
cmd input =
    case parse ast "" (pack input) of
        Left _ -> 
            liftIO $ print "No parse!"
        
        Right ast ->
            let
                expr = toExpr ast
                tp   = runInfer (infer expr)

                Right (a,constraints) = tp
                Right s = runSolver constraints
                xyz = apply s a

                abc :: Value
                abc = eval_ expr

                def = Print.value abc

                ghi = Text.concat [ def, " : ", Print.type_ xyz ]
            in
            liftIO $ do
                Text.putStrLn ghi --( (eval_ expr), Print.prnt xyz )
                --print tp


completer :: Monad m => WordCompleter m
completer n = do
    let names = ["kirk", "spock", "mccoy"]
    return $ filter (isPrefixOf n) names


help :: List String -> Repl ()
help args = 
    liftIO $ print $ "Help: " ++ show args


options :: List (String, List String -> Repl ())
options = 
    [ ("help", help)  -- :help
--    , ("say", say)    -- :say
    ]


ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"


repl :: IO ()
repl = evalRepl prompt cmd options (Just ':') (Word completer) ini
  where
    prompt = pure "> "
