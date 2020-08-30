{-# LANGUAGE TypeOperators #-}
module Tau.Repl where

import Control.Monad.Trans
import Data.Either.Extra (mapLeft, fromEither)
import Data.Functor.Const
import Data.Functor.Foldable
import Data.List (isPrefixOf)
import Data.Void
import Debug.Trace
import System.Console.Repline
import Tau.Juice
import Tau.Parser
import Text.Megaparsec

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

data ReplError
    = ParseError (ParseErrorBundle String Void)
    | TypeError TypeError
    | EvalError EvalError
    | NonExhaustivePattern
    deriving (Show, Eq)

replCommand :: String -> Repl ()
replCommand input = undefined -- putStrIO (fromEither (mapLeft show abc))
--  where
--    abc = do
--        undefined
--        expr <- mapLeft ParseError (parseExpr input)
--        pair <- mapLeft TypeError (treeTop <$> replInferType (Context mempty) expr)
--        if allPatternsAreExhaustive (fst pair)
--            then do
--                val <- mapLeft EvalError (evalExpr (compileAll (fst pair)) mempty)
--                pure (show (val, snd pair))
--            else
--                Left NonExhaustivePattern

treeTop :: AnnotatedExpr Scheme -> (Expr, Scheme)
treeTop ann = (getExpr ann, getAnnotation ann)

replInferType :: Context -> Expr -> Either TypeError (AnnotatedExpr Scheme)
replInferType context = runInfer . inferType context

replOptions :: Options Repl
replOptions =
    [ ("quit", quit)
    , ("help", help)
    ]

quit :: String -> Repl ()
quit = const (printExitMessage >> abort)

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
