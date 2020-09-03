{-# LANGUAGE TypeOperators #-}
module Tau.Repl where

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.Extra (unlessM)
import Control.Monad.Trans
import Data.Either.Extra (mapLeft, fromEither)
import Data.Functor.Const
import Data.Functor.Foldable
import Data.List (isPrefixOf)
import Data.Text (Text, pack)
import Data.Void
import Debug.Trace
import System.Console.Repline
import Tau.Env (Env(..))
import Tau.Juice
import Tau.Parser
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Tau.Env as Env

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
    = ParseError ParseError
    | TypeError TypeError
    | EvalError EvalError
    | NonExhaustivePattern
    deriving (Show, Eq)

replCommand :: String -> Repl ()
replCommand input =
    putStrIO $ case run of
        Left (ParseError err) -> 
            errorBundlePretty err

        Left err -> 
            show err

        Right r ->
            show r
  where
    run = do
        expr <- mapLeft ParseError (parseExpr (pack input))
        (expr', ty) <- mapLeft TypeError (treeTop <$> replInferType (Env mempty) expr)
        exhaustive <- allPatternsAreExhaustive expr' mempty
        unless exhaustive (Left NonExhaustivePattern)
        val <- mapLeft EvalError (evalExpr (compileAll expr') mempty)
        pure (show (val, ty))

treeTop :: AnnotatedExpr Scheme -> (Expr, Scheme)
treeTop = getExpr &&& getAnnotation

replInferType :: Env Scheme -> Expr -> Either TypeError (AnnotatedExpr Scheme)
replInferType context = runInfer . inferType context

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
