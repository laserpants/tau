{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Tau.Repl where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Text (pack, unpack)
import System.Console.Repline
import Tau.Data
import Tau.Env (Env)
import Tau.Eval
import Tau.Expr
import Tau.Parser
import Tau.Patterns (ConstructorEnv, allPatternsAreExhaustive, compileAll)
import Tau.Solver (generalize)
import Tau.Type
import Tau.Type.Inference
import Tau.Util
import Tau.Value
import Text.Megaparsec (runParser)
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env
import qualified Tau.Env.Builtin as Builtin

data ReplEnv = ReplEnv
    { values       :: ValueEnv Eval
    , typeSchemes  :: Env Scheme
    , constructors :: ConstructorEnv
    , kinds        :: Env Kind
    } deriving (Show, Eq)

unsafeParse :: Text -> Value Eval
unsafeParse text = let Right item = parseExpr text in fromJust (evalExpr item Builtin.values)

unsafeParseType :: Text -> Scheme
unsafeParseType text = let Right item = runParser scheme "" text in item

extras :: [(Text, Text)]
extras =
    [ ("fst", "\\(a, _) => a")
    , ("snd", "\\(_, b) => b") 
    , ("box", "{ x = 3 }") 
    , ("map", "\\f => \\x => let rec r = \\match | [] => [] | x :: xs => (f x) :: r xs in r x") 
    ]

typeExtras :: [(Text, Text)]
typeExtras =
    [ ("fst", "forall a b. (a, b) -> a")
    , ("snd", "forall a b. (a, b) -> b") 
    , ("box", "{ x : Int }") 
    , ("map", "forall a b. (a -> b) -> List a -> List b") 
    ]

defaultEnv :: ReplEnv
defaultEnv = ReplEnv
    { values       = Builtin.values `Env.union` Env.fromList (fmap unsafeParse <$> extras)
    , typeSchemes  = Builtin.typeSchemes `Env.union` Env.fromList (fmap unsafeParseType <$> typeExtras)
    , constructors = Builtin.constructors
    , kinds        = Builtin.kinds
    }

insertValue :: Name -> Value Eval -> ReplEnv -> ReplEnv
insertValue var val env = env{ values = Env.insert var val (values env) }

insertTypeScheme :: Name -> Scheme -> ReplEnv -> ReplEnv
insertTypeScheme var val env = env{ typeSchemes = Env.insert var val (typeSchemes env) }

type Repl = HaskelineT (StateT ReplEnv IO)

runRepl :: ReplOpts (StateT ReplEnv IO) -> IO ()
runRepl = void . flip runStateT defaultEnv . evalReplOpts

putStrIO :: (MonadIO m) => String -> HaskelineT m ()
putStrIO = liftIO . putStrLn

repl :: IO ()
repl = runRepl $ ReplOpts
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
    = RuntimeError
    | TypeError TypeError
    | NonExhaustivePatterns
    deriving (Show, Eq)

evalCommand :: Expr -> ExceptT ReplError Repl (Value Eval, Type)
evalCommand cmd = do
    ReplEnv{..} <- get
    (ty, sub, _) <- withExceptT TypeError $ liftEither $ runInferType typeSchemes cmd
    unless (allPatternsAreExhaustive cmd constructors) (throwError NonExhaustivePatterns)
    val <- maybe (throwError RuntimeError) pure (evalExpr (compileAll cmd) values)
    pure (val, apply sub ty)

replCommand :: String -> Repl ()
replCommand input =
    case parseExpr (pack input) of
        Left err ->
            putStrIO (errorBundlePretty err)

        Right result ->
            --traceShowM result
            runExceptT (evalCommand result) >>= \case
                Left err ->
                    putStrIO (show err)

                Right (val, ty) ->
                    putStrIO (unpack (prettyPrint val <> " : " <> prettyPrint ty))

letTypeCommand :: String -> Repl ()
letTypeCommand input =
    case parseDatatype ("type " <> pack input) of
        Left err ->
            putStrIO (errorBundlePretty err)

        Right ty -> do
            --traceShowM ty
            updateEnv ty
            putStrIO "Done!"

updateEnv :: Data -> Repl ()
updateEnv ty@(Sum con _ _) = do
    putStrIO (show (typeCons ty))
    modify (\ReplEnv{..} -> ReplEnv
        { values       = Env.insertMany (dataCons ty) values
        , typeSchemes  = Env.insertMany (typeCons ty) typeSchemes
        , constructors = Env.insertMany (constructorMap ty) constructors
        , kinds        = Env.insert con (typeKind ty) kinds
        , .. })

toType :: Name -> [Name] -> Type
toType con vars = foldl appT (conT con) (varT <$> vars)

constructorMap :: Data -> [(Name, Set Name)]
constructorMap (Sum _ _ prods) = [ (c, Set.fromList constrs ) | c <- constrs ] where
  constrs = (\(Prod n _) -> n) <$> prods

typeKind :: Data -> Kind
typeKind (Sum _ tvars _) = foldr arrK starK (fmap (const starK) tvars)

typeCons :: Data -> [(Name, Scheme)]
typeCons (Sum con vars prods) = fun <$> prods
  where
    fun (Prod cname ts) =
        (cname, generalize mempty [] (foldr arrT (toType con vars) ts))

dataCons :: (MonadReader (ValueEnv m) m) => Data -> [(Name, Value m)]
dataCons (Sum _ _ prods) = fun <$> prods where
    fun (Prod cname ts) = (cname, dataCon cname (length ts))

letCommand :: String -> Repl ()
letCommand input =
    case runParser parser "" (pack input) of
        Left err ->
            putStrIO (errorBundlePretty err)

        Right (var, cmd) ->
            runExceptT (evalCommand cmd) >>= \case
                Left err ->
                    putStrIO (show err)

                Right (val, ty) -> do
                    modify (insertValue var val)
                    modify (insertTypeScheme var (generalize mempty [] ty))
                    putStrIO "Done!"
  where
    parser = do
        var  <- name
        term <- symbol "=" *> expr
        pure (var, term)

envCommand :: String -> Repl ()
envCommand inp = do
    ReplEnv{..} <- get
    let key = pack inp
    putStrIO (show (Env.lookup key values))
    putStrIO (show (Env.lookup key typeSchemes))
    putStrIO (show (Env.lookup key constructors))
    putStrIO (show (Env.lookup key kinds))

replOptions :: Options Repl
replOptions =
    [ ("quit" , quit)
    , ("help" , help)
    , ("type" , letTypeCommand)
    , ("let"  , letCommand)
    , ("env"  , envCommand)
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
