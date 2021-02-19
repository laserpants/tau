{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
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
import Data.Text (Text)
import Data.Text (pack, unpack)
import System.Console.Repline
import System.Console.Repline
import Tau.Comp.Patterns
import Tau.Lang.Expr
import Tau.Eval
import Tau.Eval.Prim
import Tau.Lang.Parser
import Tau.Lang.Pretty
import Tau.PrettyTree
import Tau.Stuff
import Tau.Lang.Type
import Tau.Type.Substitution
import Tau.Util
import Text.Megaparsec (runParser)
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Data.Text as Text
import qualified Data.Set.Monad as Set
import qualified Tau.Util.Env as Env

--data ReplEnv = ReplEnv
--    { values       :: ValueEnv Eval
--    , typeSchemes  :: Env Scheme
--    , constructors :: ConstructorEnv
--    , kinds        :: Env Kind
--    } deriving (Show, Eq)

--defaultEnv :: ReplEnv
--defaultEnv = ReplEnv
--
--type Repl = HaskelineT IO)

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

stuff :: (MonadSupply Name m, MonadError String m) => PatternExpr t -> ReaderT (ClassEnv (PatternExpr NodeInfo), TypeEnv) m (Expr Type (Prep Type) Name Name)
stuff expr = do
    (tree, (sub, _)) <- runStateT (infer expr) mempty
    debugTree tree
    let tree2 = mapTags (apply sub) tree
    debugTree tree2
    (tree3, _) <- withReaderT (\(a,b) -> (a,b,[])) (runStateT (rebuildTree22 tree2) [])
    debugTree tree3
    let tree4 = simplified (mapTags nodeType tree3)
    liftEither tree4

classEnv_ = Env.fromList 
    [ ( "Num"
      , ( []
        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) [Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(+)Int")])
          ] 
        )
      )
    , ( "Show"
      , ( []
        , [ Instance [] tInt  (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tInt) [])  [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@showInt")])
          , Instance [] tBool (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [])  [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")])
          , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tList (tVar kTyp "a"))) []) [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11])
          , Instance [] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_])
          ]
        )
      )
    ]
  where
    foo11 = varExpr (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "showList"
    showPair_ = lamExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) [varPat (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"] (appExpr (NodeInfo tString []) [varExpr (NodeInfo (tString `tArr` tString `tArr` tString `tArr` tString) []) "@strconcat3", appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "a" `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "show", (appExpr (NodeInfo (tVar kTyp "a") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "a") []) "fst", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"])], litExpr (NodeInfo tString []) (LString ","), appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "b" `tArr` tString) [InClass "Show" (tVar kTyp "b")]) "show", appExpr (NodeInfo (tVar kTyp "b") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "b") []) "snd", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"]]])

typeEnv_ = Env.fromList 
    [ ( "(==)" , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
    , ( "(+)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "show" , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` tString) )
    , ( "add"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(,)"  , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1))))
    , ( "first" , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` (tGen 0)))
    , ( "second" , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` (tGen 1)))
    , ( "(::)"  , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
--    , ( "Nil"    , Forall [kTyp] [] (tList (tGen 0)) )
--    , ( "Cons"  , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "[]"    , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "length" , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )
    , ( "None"   , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )
    ]

evalEnv_ = Env.fromList 
    [ ("(+)"    , fromJust (runEval (eval plus_) mempty))
    , ("show"   , fromJust (runEval (eval show_) mempty))
    , ("(,)"    , Tau.Eval.constructor "(,)" 2) -- fromJust (runEval (eval pair) mempty))
    , ("fst"    , fromJust (runEval (eval fst_) mempty))
    , ("snd"    , fromJust (runEval (eval snd_) mempty))
    , ("(::)"   , Tau.Eval.constructor "(::)" 2)  
    , ("[]"     , Tau.Eval.constructor "[]" 0)  
    , ("length" , fromJust (runEval (eval length_) mempty))
    , ("Some"    , Tau.Eval.constructor "Some" 1)  
    , ("None"    , Tau.Eval.constructor "None" 0)  
    , ("first"  , fromJust (runEval (eval fst_) mempty))
    , ("second" , fromJust (runEval (eval snd_) mempty))
    ]
  where
    Right length_ = simplified foo26
    foo26 = lamExpr () [varPat () "x"] (litExpr () (LInt 11))

    Right snd_ = simplified foo25
    foo25 = lamExpr () [varPat () "p"] (patExpr () [varExpr () "p"] [Clause [conPat () "(,)" [anyPat (), varPat () "b"]] [] (varExpr () "b")])

    Right fst_ = simplified foo24
    foo24 = lamExpr () [varPat () "p"] (patExpr () [varExpr () "p"] [Clause [conPat () "(,)" [varPat () "a", anyPat ()]] [] (varExpr () "a")])

    Right plus_ = simplified foo1
    foo1 = lamExpr () [varPat () "d"] (patExpr () [varExpr () "d"] [ Clause [recPat () [Field () "(+)" (varPat () "(+)")]] [] (varExpr () "(+)") ])

    Right show_ = simplified foo2
    foo2 = lamExpr () [varPat () "d"] (patExpr () [varExpr () "d"] [ Clause [recPat () [Field () "show" (varPat () "show")]] [] (varExpr () "show") ])



runStuff :: PatternExpr t -> Either String (Expr Type (Prep Type) Name Name)
runStuff a = do
    x <- runExcept f
    case x of
        Nothing -> Left "error"
        Just x  -> Right x
  where
    f = runMaybeT (evalSupplyT (runReaderT (stuff a) (classEnv_, typeEnv_)) (numSupply "a"))

replCommand :: String -> HaskelineT Repl ()
replCommand input =
    case runParser expr "" (pack input) of
        Left err ->
            putStrIO (errorBundlePretty err)

        Right result -> do
            let foo = runStuff result
            case foo of
                Left err -> 
                    putStrIO (show err)

                Right r -> do
                    debugTree r
                    case evalExpr r evalEnv_ of
                        Nothing -> 
                            putStrIO "ERR"

                        Just res -> do
                            putStrIO "------------------------------------"
                            putStrIO (Text.unpack (prettyPrint result))

                            putStrIO "------------------------------------"
                            let t = exprTag r
                            let zzz = (prettyAnnValue res (toScheme t))
                            let yyy = renderDoc zzz 
                            let zzz = Text.unpack yyy
                            putStrIO zzz

            --runExceptT (evalCommand result) >>= \case
            --    Left err ->
            --        putStrIO (show err)

            --    Right (val, ty) ->
            --        putStrIO (unpack (prettyPrint val <> " : " <> prettyPrint ty))


replOptions :: Options (HaskelineT Repl)
replOptions =
    [ ("quit" , quit)
    , ("help" , help)
--    , ("type" , letTypeCommand)
--    , ("let"  , letCommand)
--    , ("env"  , envCommand)
--    , ("reset"  , resetCommand)
    ]

quit :: String -> HaskelineT Repl ()
quit = const (printExitMessage >> abort)

help :: String -> HaskelineT Repl ()
help args = putStrIO message where
    message = "Help: TODO " <> args

replCompleter :: WordCompleter Repl
replCompleter input = pure $ filter (isPrefixOf input) names where
    names =
        [ ":quit"
        , ":help"
        , ":let"
        ]

----replInitializer :: Repl ()
replInitializer = printWelcomeMessage

----replFinalizer :: Repl ExitDecision
replFinalizer = printExitMessage >> pure Exit

----printWelcomeMessage :: Repl ()
printWelcomeMessage = putStrIO "Welcome!"

printExitMessage :: HaskelineT Repl ()
printExitMessage = putStrIO "Bye!"
