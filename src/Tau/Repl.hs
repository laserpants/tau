{-# LANGUAGE OverloadedStrings     #-}
module Tau.Repl where

import Control.Monad.Reader
import Data.List (isPrefixOf)
import Data.Text (pack, unpack)
import System.Console.Repline
import Tau.Eval
import Tau.Parser
import Tau.Patterns
import Tau.Type.Inference
import Tau.Type
import Tau.Util
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Tau.Env.Builtin as Builtin

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
    case parseExpr (pack input) of
        Left err ->
            putStrIO $ errorBundlePretty err

        Right result -> do
            putStrIO $ unpack (prettyPrint result)
            -- type check

            case runInferType Builtin.typeSchemes result of
                Left err ->
                    putStrIO $ show err

                Right (ty, sub, _) ->
                    -- exhaustive check
                    if allPatternsAreExhaustive result Builtin.constructors
                        then 
                            --putStrIO (unpack (prettyPrint result))
                            case evalExpr (compileAll result) Builtin.values of
                                Nothing ->
                                    putStrIO "Runtime error"

                                Just val -> do
                                    let ty' = apply sub ty
                                    putStrIO (unpack (prettyPrint val <> " : " <> prettyPrint ty'))

                        else
                            putStrIO "Non-exhaustive patterns"

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
