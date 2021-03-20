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
import Tau.Lang.Prog
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

            a <- liftIO $ runInfer2 classEnv2 typeEnv2 (typed expr)
            case a of
                Left e ->
                    putStrIO e
                Right (r, _) ->
                    putStrIO (unpack (prettyPrint r))

typed
  :: ( MonadError String m
     , MonadIO m
     , MonadState (Substitution, Context) m
     --, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f), TypeEnv) m
     , MonadReader (ClassEnv f, TypeEnv) m
     , MonadSupply Name m ) 
  => Ast t (Op1 t) (Op2 t) f
  -> m (Maybe (Value Eval))
typed e = do
    ast <- infer e
    sub <- gets fst
    let ast2 = astApply sub ast
    liftIO $ putStrLn (showTree (nodesToString (prettyAst ast2)))
    ast4 <- evalStateT (compileClasses (desugarOperators ast2)) []
    liftIO $ putStrLn (showTree (nodesToString (prettyAst ast4)))
    case evalSupply (compileExpr (extractType ast4)) (numSupply "$") of
        Just c -> do
            liftIO $ putStrLn (showTree (nodesToString (prettyCoreTree c)))
            traceShowM c
            traceShowM (evalExpr c evalEnv2)
            pure (evalExpr c evalEnv2)
        Nothing -> 
            throwError "==fail=="

    --let ast2 = astApply sub ast
    --evalStateT (compileClasses (desugarOperators ast2)) []


--classEnv2 :: ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f)
classEnv2 :: ClassEnv f
classEnv2 = Env.fromList 
    [ ( "Num"
      , ( ( []
          , InClass "Num" "a"
          , [ ("(+)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a")
            , ("(*)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a")
            , ("(-)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a") 
            ]
          )
          -- Instances
        , [ ( []
            , InClass "Num" tInt
            , [ ("(+)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)")
              , ("(*)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)")
              , ("(-)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)")
              ]
            )
          ]
        )
      )
    , ( "Show"
      , ( ( []
          , InClass "Show" "a"
          , [ ("show", tVar kTyp "a" `tArr` tString) ]
          )
          -- Instances
        , [
          ]
        )
      )
    , ( "Ord"
      , ( ( [ InClass "Eq" "a" ]
          , InClass "Ord" "a"
          , [ ("(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool)
            , ("(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool) 
            ]
          )
          -- Instances
        , [ ( []
            , InClass "Ord" tInt
            , [ ("(>)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)")
              , ("(<)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<)")
              ]
            )
          ]
        )
      )
    ]
--    [ ( "Num"
--      , ( []
--        , "a"
--        , []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon kFun "Num") tInt) []) (fieldSet [
--              Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)")
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)")
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)")
--            ]))
----              [ Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(+)Int")
----              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(*)Int")
----              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(-)Int")
----              ])
--          ] 
--        )
--      )
--    , ( "Show"
--      , ( []
--        , "a"
--        , []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon kFun "Show") tInt) []) (fieldSet [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@Int.show")]))
--          --, Instance [] tBool (recExpr (NodeInfo (tApp (tCon kFun "Show") tBool) [])  (fieldSet [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")]))
----          , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon kFun "Show") (tList (tVar kTyp "a"))) []) (fieldSet [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11]))
--          , Instance [InClass "Show" (tVar kTyp "a"), InClass "Show" (tVar kTyp "b")] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon kFun "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) (fieldSet [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_]))
--          ]
--        )
--      )
--    , ( "Ord"
--      , ( []
--        , "a"
--        , []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon kFun "Ord") tInt) []) (fieldSet [Field (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "(>)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)")]))
--          ]
--        )
--      )
--    ]
  where
    foo11 = varExpr (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "showList"
    showPair_ = lamExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) [varPat (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"] (appExpr (NodeInfo tString []) [varExpr (NodeInfo (tString `tArr` tString `tArr` tString `tArr` tString) []) "@strconcat3", appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "a" `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "show", (appExpr (NodeInfo (tVar kTyp "a") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "a") []) "first", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"])], litExpr (NodeInfo tString []) (LString ","), appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "b" `tArr` tString) [InClass "Show" (tVar kTyp "b")]) "show", appExpr (NodeInfo (tVar kTyp "b") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "b") []) "second", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"]]])

typeEnv2 = Env.fromList 
    [ ( "(==)" , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
    , ( "(+)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(-)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "show" , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` tString) )
    , ( "add"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(,)"  , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon kFun2 "(,)") (tGen 0)) (tGen 1))))
    , ( "first" , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` (tGen 0)))
    , ( "second" , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` (tGen 1)))
    , ( "(::)"  , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
--    , ( "Nil"    , Forall [kTyp] [] (tList (tGen 0)) )
--    , ( "Cons"  , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )
    , ( "[]"    , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "length" , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )
    , ( "None"   , Forall [kTyp] [] (tApp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"   , Forall [kTyp] [] (tGen 0 `tArr` tApp (tCon kFun "Option") (tGen 0)) )

    , ( "@Int.(+)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(-)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(*)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )

    , ( "lenShow"  , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
    ]

evalEnv2 = Env.fromList 
    [ -- ("(::)"    , constructor "(::)" 2)  
    -- , -- ("[]"      , constructor "[]"   0)  
    -- , -- ("Some"    , constructor "Some" 1)  
    -- , -- ("None"    , constructor "None" 0)  
    -- , -- ("{show}"  , constructor "{show}" 1)  
    -- , -- ("{(*),(+),(-)}" , constructor "{(*),(+),(-)}" 3)  
    -- , -- ("(,)"     , constructor "(,)" 2)  
      ("show"    , fromJust (evalExpr show_ mempty))
    , ("lenShow" , fromJust (evalExpr lenShow mempty))
    , ("first"   , fromJust (runEval (eval fst_) mempty))
    , ("second"  , fromJust (runEval (eval snd_) mempty))
    , ("(+)"     , fromJust (evalExpr plus__ mempty))
--    , ("Z"       , constructor "Z" 0)
--    , ("S"       , constructor "S" 1)
    ]
  where
    lenShow = fromJust (evalSupply (compileExpr foo3) (numSupply "$"))
    show_   = fromJust (evalSupply (compileExpr foo4) (numSupply "$"))
    plus__  = fromJust (evalSupply (compileExpr foo5) (numSupply "$"))
    foo3 = lamExpr () [varPat () "d"] (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@String.length", appExpr () [varExpr () "show", varExpr () "d", varExpr () "x"]]))
    foo4 = lamExpr () [varPat () "d"] (patExpr () [varExpr () "d"] [ Clause [recPat () (fieldSet [Field () "show" (varPat () "show")])] [] (varExpr () "show") ])
    foo5 = lamExpr () [varPat () "d"] (patExpr () [varExpr () "d"] [ Clause [recPat () (fieldSet 
              [ Field () "(+)" (varPat () "x"), Field () "(*)" (anyPat ()), Field () "(-)" (anyPat ()) ])] [] (varExpr () "x") ])
    fst_ = fromJust (evalSupply (compileExpr foo24) (numSupply "$"))
    snd_ = fromJust (evalSupply (compileExpr foo25) (numSupply "$"))
    foo24 = lamExpr () [varPat () "p"] (patExpr () [varExpr () "p"] [Clause [conPat () "(,)" [varPat () "a", anyPat ()]] [] (varExpr () "a")])
    foo25 = lamExpr () [varPat () "p"] (patExpr () [varExpr () "p"] [Clause [conPat () "(,)" [varPat () "zz", varPat () "b"]] [] (varExpr () "b")])
 

--runInfer2 :: ClassEnv c -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv c, TypeEnv) (SupplyT Name (ExceptT String (MaybeT IO)))) a -> x -- Either String (a, (Substitution, Context))
--runInfer2 :: ClassEnv c -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv c, TypeEnv) (SupplyT Name (ExceptT String (MaybeT IO)))) a -> IO (Either String (a, (Substitution, Context)))
runInfer2 :: ClassEnv f -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv f, TypeEnv) (SupplyT Name (ExceptT String (MaybeT IO)))) a -> IO (Either String (a, (Substitution, Context)))
runInfer2 e1 e2 = 
    flip runStateT (mempty, mempty)
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> runMaybeT 
        >>> fmap (fromMaybe (Left "error"))


