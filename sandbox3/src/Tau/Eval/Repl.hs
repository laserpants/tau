{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
module Tau.Eval.Repl where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Text (pack, unpack)
import System.Console.Repline
import Tau.Lang.Parser
import Tau.Pretty
import Tau.Util
import Text.Megaparsec (runParser)
import Text.Megaparsec.Error (errorBundlePretty)
import System.Console.Repline
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

data ReplEnv = ReplEnv
--    { values       :: ValueEnv Eval
--    , typeSchemes  :: Env Scheme
--    , constructors :: ConstructorEnv
--    , kinds        :: Env Kind
--    } deriving (Show, Eq)

defaultEnv :: ReplEnv
defaultEnv = ReplEnv

type Repl = HaskelineT (StateT ReplEnv IO)

runRepl :: ReplOpts (StateT ReplEnv IO) -> IO ()
runRepl = void . flip runStateT defaultEnv . evalReplOpts

putStrIO :: (MonadIO m) => String -> HaskelineT m ()
putStrIO = liftIO . putStrLn

repl :: IO ()
repl = runRepl $ ReplOpts
    { banner           = const (pure "Tau > ")
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
    case runParser expr "" (pack input) of
        Left err ->
            putStrIO "err" -- (errorBundlePretty err)

        Right result -> do
            traceShowM result
            traceShowM (pretty result)
--            runExceptT (evalCommand result) >>= \case
--                Left err ->
--                    putStrIO (show err)
--
--                Right (val, ty) ->
--                    putStrIO (unpack (prettyPrint val <> " : " <> prettyPrint ty))


replOptions :: Options Repl
replOptions =
    [ ("quit" , quit)
    , ("help" , help)
--    , ("type" , letTypeCommand)
--    , ("let"  , letCommand)
--    , ("env"  , envCommand)
--    , ("reset"  , resetCommand)
    ]

quit :: String -> Repl ()
quit = const (printExitMessage >> abort)

help :: String -> Repl ()
help args = putStrIO message where
    message = "Help: TODO " <> args

replCompleter :: WordCompleter (StateT ReplEnv IO)
replCompleter input = pure $ filter (isPrefixOf input) names where
    names =
        [ ":quit"
        , ":help"
        , ":let"
        ]

replInitializer :: Repl ()
replInitializer = printWelcomeMessage

replFinalizer :: Repl ExitDecision
replFinalizer = printExitMessage >> pure Exit

printWelcomeMessage :: Repl ()
printWelcomeMessage = putStrIO "Welcome!"

printExitMessage :: Repl ()
printExitMessage = putStrIO "Bye!"
