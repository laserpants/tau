{-# LANGUAGE OverloadedStrings     #-}
module Tau.Repl where

import Control.Monad.Reader
import Data.List (isPrefixOf)
import Data.Text (pack, unpack)
import System.Console.Repline
import Tau.Env (Env)
import Tau.Eval
import Tau.Parser
import Tau.Patterns
import Tau.Type.Inference
import Tau.Type
import Tau.Util
import Tau.Value
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Tau.Env as Env

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

            case runInferType replTypeEnv result of
                Left err ->
                    putStrIO $ show err

                Right (ty, sub, _) ->
                    -- exhaustive check
                    if allPatternsAreExhaustive result replConstructorEnv
                        then do
                            --putStrIO (unpack (prettyPrint result))
                            case evalExpr (compileAll result) replValueEnv of
                                Nothing ->
                                    putStrIO "Runtime error"

                                Just val -> do
                                    let ty' = apply sub ty
                                    putStrIO (unpack (prettyPrint val <> " : " <> prettyPrint ty'))

                        else
                            putStrIO "Non-exhaustive patterns"

--data Environments = Environments
--    { constructorEnv :: ConstructorEnv
--    , valueEnv       :: ValueEnv
--    , optionsEnv     :: Options Repl
--    }
--
--environments :: Environments
--environments = Environments
--    { constructorEnv =
--        [ ("Nil"  , ["Nil", "Cons"])
--        , ("Cons" , ["Nil", "Cons"])
--        ]
--    , valueEnv =
--        [ ("Cons"   , dataCon "Cons" 2)
--        , ("Nil"    , dataCon "Nil" 0)
--        ]
--    , optionsEnv =
--        [ ("quit", quit)
--        , ("help", help)
--        ]
--    }

replTypeEnv :: Env Scheme
replTypeEnv = Env.fromList
    [ ("Nil"    , Forall ["a"] [] list)
    , ("Cons"   , Forall ["a"] [] (arrT (varT "a") (arrT list list)))
    , ("Show"   , Forall ["a"] [] (arrT (arrT (varT "a") (conT "String")) (appT (conT "Show") (varT "a"))))
    , ("Tuple2" , Forall ["a", "b"] [] (arrT (varT "a") (arrT (varT "b") (appT (appT (conT "Tuple2") (varT "a")) (varT "b")))))
    ]
  where
    list = appT (conT "List") (varT "a")

replConstructorEnv :: ConstructorEnv
replConstructorEnv = constructorEnv
    [ ("Nil"    , ["Nil", "Cons"])
    , ("Cons"   , ["Nil", "Cons"])
    , ("Tuple2" , ["Tuple2"])
    ]

replValueEnv :: ValueEnv Eval
replValueEnv = Env.fromList
    [ ("Cons"   , dataCon "Cons" 2)
    , ("Nil"    , dataCon "Nil" 0)
    , ("Tuple2" , dataCon "Tuple2" 2)
    ]

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
