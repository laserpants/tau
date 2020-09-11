module Tau.Repl where

import Control.Monad.Except
import Data.List (isPrefixOf)
import Data.Text (pack, unpack)
import System.Console.Repline
import Tau.Parser
import Tau.Util
import Text.Megaparsec.Error (errorBundlePretty)

type Repl = HaskelineT IO

putStrIO :: (MonadIO m) => String -> HaskelineT m ()
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
replCommand input =
    putStrIO $ case parseExpr (pack input) of
        Left err ->
            errorBundlePretty err

        Right result ->
            unpack (prettyPrint result)

replOptions :: Options Repl
replOptions =
    [ ("quit", quit)
    , ("help", help)
    ]

quit :: String -> Repl ()
quit = const (printExitMessage >> abort)

help :: String -> Repl ()
help args = putStrIO message where
    message = "Help: TODO " <> args

replCompleter :: WordCompleter IO
replCompleter input = pure $ filter (isPrefixOf input) names where
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
