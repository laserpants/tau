module Tau.Repl where

import Control.Monad.Trans
import Data.List (isPrefixOf)
import System.Console.Repline
import System.Process (system)


type Repl a = HaskelineT IO a


cmd :: String -> Repl ()
cmd input = liftIO $ print input


completer :: Monad m => WordCompleter m
completer n = do
    let names = ["kirk", "spock", "mccoy"]
    return $ filter (isPrefixOf n) names


help :: [String] -> Repl ()
help args = 
    liftIO $ print $ "Help: " ++ show args


say :: [String] -> Repl ()
say args = do
    liftIO $ system $ "cowsay" ++ " " ++ (unwords args)
    return ()


options :: [(String, [String] -> Repl ())]
options = 
    [ ("help", help)  -- :help
    , ("say", say)    -- :say
    ]


ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"


repl :: IO ()
repl = evalRepl (pure "> ") cmd options (Just ':') (Word completer) ini
