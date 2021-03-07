{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval.Repl where

import Control.Exception
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Data.List (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text, pack, unpack)
import System.Console.Repline
import Tau.Comp.Core
import Tau.Comp.Type.Substitution
import Tau.Eval.Core
import Tau.Eval.Prim
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Pretty
import Tau.Lang.Pretty.Ast
import Tau.Lang.Type
import Tau.Util
import Text.Megaparsec (runParser)
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

newtype Repl a = Repl { unRepl :: IO a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadIO 
    , MonadThrow
    , MonadCatch
    , MonadMask 
    )

runRepl :: ReplOpts Repl -> IO ()
runRepl = unRepl . evalReplOpts

putStrIO :: (MonadIO m) => String -> HaskelineT m ()
putStrIO = liftIO . putStrLn

repl :: IO ()
repl = runRepl $ ReplOpts
    { banner           = const (pure "<Tau> ")
    , command          = replCommand 
    , options          = replOptions
    , prefix           = Just ':'
    , multilineCommand = Nothing
    , tabComplete      = Word0 replCompleter
    , initialiser      = replInitializer
    , finaliser        = replFinalizer
    }

replCompleter :: WordCompleter Repl
replCompleter input = pure $ filter (isPrefixOf input) names where
    names =
        [ ":quit"
        , ":help"
        , ":let"
        ]

quit :: String -> HaskelineT Repl ()
quit = const (printExitMessage >> abort)

help :: String -> HaskelineT Repl ()
help args = putStrIO message where
    message = "Help: TODO " <> args

replOptions :: Options (HaskelineT Repl)
replOptions =
    [ ("quit" , quit)
    , ("help" , help)
--    , ("type" , letTypeCommand)
--    , ("let"  , letCommand)
--    , ("env"  , envCommand)
--    , ("reset"  , resetCommand)
    ]

replInitializer :: HaskelineT Repl ()
replInitializer = printWelcomeMessage

replFinalizer :: HaskelineT Repl ExitDecision
replFinalizer = printExitMessage >> pure Exit

printWelcomeMessage :: HaskelineT Repl ()
printWelcomeMessage = putStrIO "Welcome!"

printExitMessage :: HaskelineT Repl ()
printExitMessage = putStrIO "Bye!"

replCommand :: String -> HaskelineT Repl ()
replCommand input =
    pure ()
