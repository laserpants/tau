{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Eval.Repl where

import Control.Arrow ((>>>))
import Control.Exception
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Data.List (isPrefixOf)
import Data.Maybe (fromJust, fromMaybe)
import Data.Set.Monad (Set)
import Data.Text (Text, pack, unpack)
import Data.Tree.View (showTree)
import Data.Void
import System.Console.Repline
import Tau.Comp.Core
import Tau.Comp.Type.Inference
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
    case runParser expr "" (pack input) of
        Left err -> 
            putStrIO (errorBundlePretty err)

        Right expr -> do
            putStrIO "Parse"
            putStrIO (unpack (prettyPrint expr))

            liftIO $ runInfer2 classEnv2 typeEnv2 (typed expr)

            --putStrIO (show ast)
            --putStrIO (show ast)
            pure ()


typed e = do
    ast <- infer e
    sub <- gets fst
    let ast2 = astApply sub ast
    liftIO $ putStrLn (showTree (nodesToString (prettyAst ast2)))
    ast4 <- evalStateT (compileClasses (desugarOperators ast2)) []
    liftIO $ putStrLn (showTree (nodesToString (prettyAst ast4)))
    compileExpr (extractType ast4)
    --let ast2 = astApply sub ast
    --evalStateT (compileClasses (desugarOperators ast2)) []

classEnv2 = Env.fromList []

typeEnv2 = Env.fromList []

--runInfer2 :: ClassEnv c -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv c, TypeEnv) (SupplyT Name (ExceptT String (MaybeT IO)))) a -> x -- Either String (a, (Substitution, Context))
runInfer2 :: ClassEnv c -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv c, TypeEnv) (SupplyT Name (ExceptT String (MaybeT IO)))) a -> IO (Either String (a, (Substitution, Context)))
runInfer2 e1 e2 = 
    flip runStateT (mempty, mempty)
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        -- >>> fromMaybe (Left "error")
        >>> runMaybeT -- (Left "error")
        >>> fmap (fromMaybe (Left "error"))


