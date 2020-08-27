module Tau.Repl where

import Control.Monad.Trans
import Data.List (isPrefixOf)
import System.Console.Repline
import Tau.Parser

type Repl = HaskelineT IO

putStrIO :: String -> HaskelineT IO ()
putStrIO = liftIO . putStrLn

repl :: IO ()
repl = evalReplOpts $ ReplOpts
    { banner           = const (pure "> ")
    , command          = replCommand
    , options          = replOptions
    , prefix           = Just ':'
    , multilineCommand = Nothing
    , tabComplete      = Word0 replCompleter
    , initialiser      = replInitializer
    , finaliser        = replFinalizer
    }

replCommand :: String -> Repl ()
replCommand input = do
    let expr = parseExpr input
    case expr of
        Left err ->
           putStrIO "Error" 

        Right r ->
            putStrIO (show r)

replOptions :: Options Repl
replOptions = 
    [ ("quit", quit)
    , ("help", help)
    ]

quit :: String -> Repl ()
quit _ = printExitMessage >> abort

help :: String -> Repl ()
help args = putStrIO message
  where
    message = "Help: TODO " <> args

replCompleter :: WordCompleter IO
replCompleter input = pure $ filter (isPrefixOf input) names
  where 
    names =
        [ ":quit"
        , ":help"
        ]

replInitializer :: Repl ()
replInitializer = printWelcomeMessage

replFinalizer :: Repl ExitDecision
replFinalizer = printExitMessage >> pure Exit

printWelcomeMessage :: Repl ()
printWelcomeMessage = putStrIO "Welcome!"

printExitMessage :: Repl ()
printExitMessage = putStrIO "Bye!" 
