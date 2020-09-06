{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}
module Tau.Repl where

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.Extra (unlessM)
import Control.Monad.Trans
import Data.Either.Extra (mapLeft, fromEither)
import Data.Functor.Const
import Data.Functor.Foldable
import Data.List (isPrefixOf)
import Data.Text (Text, pack, unpack)
import Data.Void
import Debug.Trace
import System.Console.Repline
import Tau.Env (Env(..))
import Tau.Juice
import Tau.Parser
import Tau.Print
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Tau.Env as Env

type Repl = HaskelineT IO

putStrIO :: String -> HaskelineT IO ()
putStrIO = liftIO . putStrLn

putTextIO :: Text -> HaskelineT IO ()
putTextIO = putStrIO . unpack 

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
    case run of
        Left (ParseError err) -> 
            putStrIO (errorBundlePretty err)

        Left err -> 
            putStrIO (show err)

        Right (val, ty) -> 
            putTextIO (prettyPrint val <> " : " <> prettyPrint ty)
  where
    run = do
        expr <- mapLeft ParseError (parseExpr (pack input))
        (expr', ty) <- mapLeft TypeError (treeTop <$> replInferType replTypeEnv expr)
        exhaustive <- allPatternsAreExhaustive expr' replConstructorEnv
        unless exhaustive (Left NonExhaustivePattern)
        val <- mapLeft EvalError (evalExpr (compileAll expr') replEvalEnv)
        pure (val, ty)

replTypeEnv :: Env Scheme
replTypeEnv = Env.fromList
    [ ("Nil"  , Forall ["a"] [] list)
    , ("Cons" , Forall ["a"] [] (arrT (varT "a") (arrT list list))) ]
  where
    list = appT (conT "List") (varT "a")

replEvalEnv :: EvalEnv Eval
replEvalEnv = Env.fromList
    [ ("Cons"   , dataCon "Cons" 2)
    , ("Nil"    , dataCon "Nil" 0) ]

replConstructorEnv :: ConstructorEnv
replConstructorEnv = constructorEnv
    [ ("Nil"  , ["Nil", "Cons"])
    , ("Cons" , ["Nil", "Cons"]) ]

-- ===============================

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
printWelcomeMessage = putStrIO "Welcome!\nFlow with the universe — like a ship on a vast and majestic river."

printExitMessage :: Repl ()
printExitMessage = putStrIO "Bye!"
