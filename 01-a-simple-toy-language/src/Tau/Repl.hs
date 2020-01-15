{-# LANGUAGE OverloadedStrings #-}
module Tau.Repl where

import Control.Monad.Reader
import Data.List (isPrefixOf)
import Data.Text (Text, pack)
import System.Console.Repline
import Tau.Core
import Tau.Core.Parser
import Tau.Eval
import Tau.Type
import Tau.Type.Unify
import Tau.Util
import Text.Megaparsec (parse)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Tau.Util.Print as Print


type Repl a = HaskelineT IO a


evald :: Ast -> Value
evald ast = runReader (eval (toExpr ast)) mempty


typeOf :: Ast -> Either String Type
typeOf ast = do
    ( t1, cs ) <- runInfer (infer (toExpr ast))
    apply <$> runSolver cs <*> pure t1


cmd :: String -> Repl ()
cmd input =
    liftIO $ case parse ast "" (pack input) of
        Left _ ->
            putStrLn "I didn't understand that."

        Right ast ->
            case typeOf ast of
                Left err ->
                    putStrLn err

                Right type_ ->
                    let
                        output = Text.concat
                            [ Print.value (evald ast)
                            , " : "
                            , Print.type_ type_
                            ]
                    in
                    Text.putStrLn output


completer :: Monad m => WordCompleter m
completer n =
    pure $ filter (isPrefixOf n) names
  where
    names =
        [ ":help"
        , ":quit"
        ]


help :: List String -> Repl ()
help args =
    liftIO (putStrLn message)
  where
    message = "Help: " ++ show args


quit :: List String -> Repl ()
quit args =
    liftIO (putStrLn "Bye!") >> abort


options :: List (String, List String -> Repl ())
options =
    [ ( "help", help )
    , ( "quit", quit )
    ]


ini :: Repl ()
ini = liftIO (putStrLn "A toy language")


repl :: IO ()
repl = evalRepl prompt cmd options (Just ':') (Word completer) ini
  where
    prompt = pure "> "
