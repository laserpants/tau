{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Control.Monad.Writer hiding (Sum)
import Data.Function ((&))
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Maybe
import Data.Set.Monad (Set)
import Data.Text (Text)
import Data.Tree.View (showTree)
import Data.Tuple.Extra (both)
import Data.Void
import Tau.Comp.Core
import Tau.Comp.Prog
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution (Substitution, apply)
import Tau.Comp.Type.Unification
import Tau.Eval.Core
import Tau.Eval.Repl
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Parser2
import Tau.Lang.Pretty.Ast
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Util.Env as Env

--noDups = undefined
--
--mapPairs :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name Void Void)
--mapPairs =
--    matchAlgo
--        [varExpr () "u1", varExpr () "u2", varExpr () "u3"] 
--        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "e1")
--        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (varExpr () "e2")
--        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
--        ]
--        (varExpr () "FAIL")
--
--mapPairs2 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name Void Void)
--mapPairs2 =
--    matchAlgo
--        [varExpr () "u2", varExpr () "u3"] [ Clause [conPat () "[]" [], varPat () "ys"] [] (varExpr () "e1")
--        , Clause [conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (varExpr () "e2")
--        , Clause [conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
--        ]
--        (varExpr () "FAIL")
--
--mapPairs3 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name Void Void)
--mapPairs3 =
--    matchAlgo
--        [varExpr () "u2"] 
--        [ Clause [conPat () "[]" []] [] (varExpr () "e1")
----        , Clause [varPat () "x", varPat () "xs", conPat () "[]" []] [] (varExpr () "e2")
----        , Clause [varPat () "x", varPat () "xs", conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
--        ]
--        (varExpr () "FAIL")
--
--
--mapPairs4 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name Void Void)
--mapPairs4 =
--    matchAlgo
--        [] 
--        [ Clause [] [] (varExpr () "e2")
--        ]
--        (varExpr () "FAIL")
--
--
--
--test1 = evalSupply mapPairs (numSupply "$")
--
--
--test2 = evalSupply (compileExpr e) (numSupply "$")
--  where
--    e = appExpr ()
--            [ lamExpr () [varPat () "x"]
--                (patExpr () [varExpr () "x"]
--                    [ Clause [litPat () (TInt 5)] [] (litExpr () (TInt 1))
--                    , Clause [varPat () "y"] [] (litExpr () (TInt 2)) ])
--            , litExpr () (TInt 5) ]
--
--test22 = case test2 of
--    Just c -> do
--        traceShowM c
--        evalExpr c mempty
--
--test3 = evalSupply (compileExpr e) (numSupply "$")
--  where 
--    e = patExpr () [litExpr () (TInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (TInt 9), conExpr () "[]" []]]
--        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "ys")
--        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (litExpr () (TString "e2"))
--        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (litExpr () (TString "e3"))
--        ]
--
--test33 = case test3 of
--    Just c -> do
--        traceShowM c
--        evalExpr c evalEnv

evalEnv = Env.fromList 
--    [ ("(::)"    , constructor "(::)" 2)  
--    , ("[]"      , constructor "[]"   0)  
--    , ("Some"    , constructor "Some" 1)  
--    , ("None"    , constructor "None" 0)  
--    , ("{show}"  , constructor "{show}" 1)  
--    , ("{(*),(+),(-)}" , constructor "{(*),(+),(-)}" 3)  
--    , ("(,)"     , constructor "(,)" 2)  
    [ ("show"    , fromJust (evalExpr show_ mempty))
    , ("lenShow" , fromJust (evalExpr lenShow mempty))
    , ("first"   , fromJust (runEval (eval fst_) mempty))
    , ("second"  , fromJust (runEval (eval snd_) mempty))
    , ("(+)"     , fromJust (evalExpr plus__ mempty))
    , ("(?)"     , fromJust (evalExpr opt__ mempty))
    , ("(++)"    , fromJust (evalExpr (cVar "@(++)") mempty)) -- PrimFun "@(++)")
--    , ("Z"       , constructor "Z" 0)  
--    , ("S"       , constructor "S" 1)  
    ]
  where
    lenShow = fromJust (evalSupply (compileExpr foo3) (numSupply "$"))
    show_   = fromJust (evalSupply (compileExpr foo4) (numSupply "$"))
    plus__  = fromJust (evalSupply (compileExpr foo5) (numSupply "$"))
    opt__   = fromJust (evalSupply (compileExpr foo6) (numSupply "$"))
    foo3 = lamExpr () [varPat () "d"] (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@String.length", appExpr () [varExpr () "show", varExpr () "d", varExpr () "x"]]))
    foo4 = lamExpr () [varPat () "d"] (patExpr () [varExpr () "d"] [ Clause [recPat () (fieldSet [Field () "show" (varPat () "show")])] [] (varExpr () "show") ])
    foo5 = lamExpr () [varPat () "d"] (patExpr () [varExpr () "d"] [ Clause [recPat () (fieldSet 
              [ Field () "(+)" (varPat () "x"), Field () "(*)" (anyPat ()), Field () "(-)" (anyPat ()) ])] [] (varExpr () "x") ])
    fst_ = fromJust (evalSupply (compileExpr foo24) (numSupply "$"))
    snd_ = fromJust (evalSupply (compileExpr foo25) (numSupply "$"))
    foo24 = lamExpr () [varPat () "p"] (patExpr () [varExpr () "p"] [Clause [conPat () "(,)" [varPat () "a", anyPat ()]] [] (varExpr () "a")])
    foo25 = lamExpr () [varPat () "p"] (patExpr () [varExpr () "p"] [Clause [conPat () "(,)" [varPat () "zz", varPat () "b"]] [] (varExpr () "b")])
    foo6 = lamExpr () [varPat () "a", varPat () "b"] (patExpr () [varExpr () "a"] [ Clause [conPat () "Some" [varPat () "x"]] [] (varExpr () "x"), Clause [anyPat ()] [] (varExpr () "b")])
 

---- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
--test4 = evalSupply (compileExpr e) (numSupply "$")
--  where 
--    e = letExpr () (BLet (varPat () "f")) (patExpr () [] 
--        [ Clause [litPat () (TInt 0)] [] (litExpr () (TInt 1))
--        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (TInt 1)]]])
--      ]) (appExpr () [varExpr () "f", litExpr () (TInt 5)]) 
--
----    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (TInt 1)]])
--
--test44 = case test4 of
--    Just c -> do
--        traceShowM c
--        evalExpr c evalEnv
--
--
---- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
--test5 = evalSupply (compileExpr e) (numSupply "$")
--  where 
--    e = fixExpr () "f" (patExpr () [] 
--        [ Clause [litPat () (TInt 0)] [] (litExpr () (TInt 1))
--        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (TInt 1)]]])
--      ]) (appExpr () [varExpr () "f", litExpr () (TInt 10)]) 
--
----    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (TInt 1)]])
--
--test55 = case test5 of
--    Just c -> do
--        traceShowM c
--        evalExpr c evalEnv
--
--
--
--type Infer a = StateT (Substitution, Context) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv f g c d -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv f g c d, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a -> Either String (a, (Substitution, Context))
runInfer e1 e2 = 
    flip runStateT (mempty, mempty)
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "error")

--test6 =
--    runInfer classEnv typeEnv f
--  where
--    f :: Infer (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo))
--    f = infer e
----    e = appExpr ()
----            [ lamExpr () [varPat () "x"]
----                (patExpr () [varExpr () "x"]
----                    [ Clause [litPat () (TInt 5)] [] (litExpr () (TInt 1))
----                    , Clause [varPat () "y"] [] (litExpr () (TInt 2)) ])
----            , litExpr () (TInt 5) ]
--
--    -- match 5 [] (9 :: []) with
--    --   | f []        ys        => ys
--    --   | f (x :: xs) []        => e2
--    --   | f (x :: xs) (y :: ys) => ys
--    -- 
--    e = patExpr () [litExpr () (TInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (TInt 9), conExpr () "[]" []]]
--        [ Clause [varPat () "f" , conPat () "[]" []                                , varPat () "ys"] 
--              [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 8))]    
--              (varExpr () "ys")
--        , Clause [varPat () "f" , conPat () "(::)" [varPat () "x", varPat () "xs"] , conPat () "[]" []] [] 
--              (conExpr () "[]" [])
--        , Clause [varPat () "f" , conPat () "(::)" [varPat () "x", varPat () "xs"] , conPat () "(::)" [varPat () "y", varPat () "ys"]] [] 
--              (varExpr () "ys")
--        ]
--
--
--test66 = let Right (ast, (sub, _)) = test6 in putStrLn (showTree (nodesToString (prettyAst (mapTags (apply sub) (mapTags nodeType ast)))))
--
--
--test7 =
--    runInfer classEnv typeEnv f
--  where
--    f :: Infer (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo))
--    f = infer e
--    e = fixExpr () "f" (patExpr () [] 
--        [ Clause [litPat () (TInt 0)] [] (litExpr () (TInt 1))
--        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (TInt 1)]]])
--      ]) (appExpr () [varExpr () "f", litExpr () (TInt 5)]) 
--
--test77 = 
--    case test7 of
--        Left e -> error e
--        Right (ast, (sub, _)) -> 
--            putStrLn (showTree (nodesToString (prettyAst (mapTags (apply sub) (mapTags nodeType ast)))))
--
--
----test1 = runSupply e (numSupply "$")
----  where
----    e :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
----    e = compileExpr mapPairs
--
--
--test8 =
--    runInfer classEnv typeEnv f
--  where
--    f :: Infer (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo))
--    f = infer e
--    -- let g x (Some y) = \z => z in g (Some 5) ()
--    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (dotExpr () "baz" (litExpr () (TInt 5)))
--    --e = letExpr () (BFun "baz" [varPat () "x"]) (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (TInt 1)]) (dotExpr () "baz" (litExpr () (TInt 5)))
--    --e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (TInt 1)])) (dotExpr () "baz" (litExpr () (TInt 5)))
----    e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (TInt 1)])) (appExpr () [varExpr () "baz", litExpr () (TInt 5)])
----    e = letExpr () (BFun "g" [varPat () "x", conPat () "Some" [varPat () "y"]]) (lamExpr () [varPat () "z"] (varExpr () "z"))
----        (appExpr () [varExpr () "g", litExpr () (TInt 1), conExpr () "Some" [litExpr () (TInt 5)], litExpr () TUnit])
--         
--
--test88 = 
--    case test8 of
--        Left e -> error e
--        Right (ast, (sub, _)) -> do
--            traceShowM ast
--            traceShowM "^^^^^^^^^^^^^^"
--            traceShowM (mapTags nodeType ast)
--            traceShowM "^^^^^^^^^^^^^^"
--            traceShowM (mapTags (apply sub) (mapTags nodeType ast))
--            traceShowM "^^^^^^^^^^^^^^"
--            traceShowM "^^^^^^^^^^^^^^"
--            putStrLn (showTree (nodesToString (prettyAst (mapTags (apply sub) (mapTags nodeType ast)))))
--
--
--test888 = 
--    case evalSupply (compileExpr e) (numSupply "$") of
--        Just c -> evalExpr c evalEnv
--  where
----    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (TInt 1))) (dotExpr () "baz" (litExpr () (TInt 5)))
----    e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (TInt 1)])) (appExpr () [varExpr () "baz", litExpr () (TInt 5)])
----    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (TInt 1))) (dotExpr () "baz" (litExpr () (TInt 5)))
--
----    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (TInt 1))) (dotExpr () "baz" (litExpr () (TInt 5)))
-- 
--    e = letExpr () (BFun "baz" [varPat () "x"]) (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (TInt 1)]) (dotExpr () "baz" (litExpr () (TInt 5)))
--
--
--test9 =
--    runInfer classEnv typeEnv f
--  where
--    f :: Infer (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo))
--    f = infer e
--    -- let g x (Some y) = \z => z in g (Some 5) ()
--    e = appExpr () 
--        [ lamExpr () [conPat () "Some" [varPat () "s"], conPat () "(::)" [varPat () "x", varPat () "xs"]] (varExpr () "s")
--        , conExpr () "Some" [litExpr () (TInt 5)]
--        , conExpr () "(::)" [litExpr () (TInt 3), conExpr () "[]" []]
--        ]
--
--
--test99 = 
--    case test9 of
--        Left e -> error e
--        Right (ast, (sub, _)) -> 
--            putStrLn (showTree (nodesToString (prettyAst (mapTags (apply sub) (mapTags nodeType ast)))))
--
--
--test999 = 
--    case evalSupply (compileExpr e) (numSupply "$") of
--        Just c -> evalExpr c evalEnv
--  where
--    e = appExpr () 
--        [ lamExpr () [conPat () "Some" [varPat () "s"], conPat () "(::)" [varPat () "x", varPat () "xs"]] (varExpr () "s")
--        , conExpr () "Some" [litExpr () (TInt 5)]
--        , conExpr () "(::)" [litExpr () (TInt 3), conExpr () "[]" []]
--        ]

testExpr2 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr2 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")

testExpr3 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr3 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (TInt 5)])

testExpr4 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr4 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])

testExpr5 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr5 = lamExpr () [varPat () "x"] (letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))

testExpr6 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr6 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))

testExpr7 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr7 = appExpr () [varExpr () "lenShow", litExpr () (TInt 12345)]

testExpr8 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr8 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])

testExpr9 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr9 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")

-- let f x = lenShow in f ()
testExpr10 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr10 = letExpr () (BFun "f" [varPat () "x"]) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () TUnit])

-- let p = (5, 1) in show p
testExpr11 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr11 = letExpr () (BLet (varPat () "p")) (conExpr () "(,)" [litExpr () (TInt 5), litExpr () (TInt 1)]) (appExpr () [varExpr () "show", varExpr () "p"])

-- \x => show (x, x)
testExpr12 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr12 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", conExpr () "(,)" [varExpr () "x", varExpr () "x"]])

--testExpr21 = op2Expr () OAdd (litExpr () (LFloat 3.1)) (litExpr () (LFloat 4.1)) 
testExpr21 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr21 = op2Expr () (OAdd ()) (litExpr () (TInt 3)) (litExpr () (TInt 4)) 

testExpr22 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr22 = appExpr () [patExpr () [] [
      Clause [ conPat () "(::)" [litPat () (TInt 2), varPat () "z"]
             , varPat () "y" ] [] (litExpr () (TString "one")) 
    , Clause [ varPat () "x"       
             , litPat () (TInt 4) ] [] (litExpr () (TString "two")) 
    , Clause [ conPat () "(::)" [anyPat (), anyPat ()]
             , varPat () "x" ] [] (litExpr () (TString "three"))
    ], conExpr () "(::)" [litExpr () (TInt 3), conExpr () "[]" []], litExpr () (TInt 4)]

testExpr23 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr23 = appExpr () [letExpr () (BFun "f" [varPat () "x"]) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () TUnit]), litExpr () (TInt 873)] 

testExpr24 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr24 = appExpr () [lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", conExpr () "(,)" [varExpr () "x", varExpr () "x"]]), litExpr () (TInt 11)]

testExpr25 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d 
testExpr25 = appExpr () [patExpr () [] [
      Clause [ conPat () "(::)" [varPat () "z", varPat () "zs"]
             , varPat () "y" ] 
             [ op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInt 2)), op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInt 2))] 
             (litExpr () (TString "one")) 
    , Clause [ anyPat () 
             , anyPat () ] 
             [] 
             (litExpr () (TString "two")) 
    ], conExpr () "(::)" [litExpr () (TInt 3), conExpr () "[]" []], litExpr () (TInt 4)]

testExpr26 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr26 = appExpr () [patExpr () [] [
      Clause [ conPat () "(::)" [varPat () "z", varPat () "zs"]
             , varPat () "y" ] 
             [ op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInt 2)), op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInt 2))] 
             (litExpr () (TString "one")) 
    , Clause [ anyPat () 
             , anyPat () ] 
             [] 
             (litExpr () (TString "two")) 
    ], conExpr () "(::)" [litExpr () (TInt 1), conExpr () "[]" []], litExpr () (TInt 4)]

testExpr26b :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr26b = patExpr () [] [
      Clause [ conPat () "(::)" [varPat () "z", varPat () "zs"]
             , varPat () "y" ] 
             [ op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInt 2)), op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInt 2))] 
             (litExpr () (TString "one")) 
    , Clause [ anyPat () 
             , anyPat () ] 
             [] 
             (litExpr () (TString "two")) ]

-- let map f xs = fix mu = fun [] => [] | x :: xs => f x :: mu xs in mu xs
testExpr27 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr27 = -- fixExpr () "map" (patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (conExpr () "(::)" [undefined, appExpr () [varExpr () "map", varExpr () "f", varExpr () "xs"]]), Clause [conPat () "[]" []] [] (conExpr () "[]" [])]) 
    (letExpr () (BFun "map" [varPat () "f", varPat () "xs"]) (fixExpr () "mu" (patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], appExpr () [varExpr () "mu", varExpr () "xs"]]), Clause [conPat () "[]" []] [] (conExpr () "[]" [])]) (appExpr () [varExpr () "mu", varExpr () "xs"]))
          (letExpr () (BLet (varPat () "xs")) (conExpr () "(::)" [litExpr () (TInt 1), conExpr () "(::)" [litExpr () (TInt 2), conExpr () "(::)" [litExpr () (TInt 3), conExpr () "[]" []]]]) (dotExpr () (varExpr () "xs") (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))]))))

testExpr28 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr28 = appExpr () [patExpr () [] [Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True)), Clause [anyPat ()] [] (litExpr () (TBool False))], conExpr () "(::)" [litExpr () (TInt 1), conExpr () "[]" []]]

-- (fun | _ :: _ => True | _ => False) []
testExpr29 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr29 = appExpr () [patExpr () [] [Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True)), Clause [anyPat ()] [] (litExpr () (TBool False))], conExpr () "[]" []]

testExpr30 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr30 = patExpr () [] [Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True)), Clause [varPat () "x"] [] (litExpr () (TBool False))]

testExpr31 = evalSupply (compilePatterns [varExpr () "x"] 
    [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True))
    , Clause [varPat () "a"] [] (litExpr () (TBool False))
--    , Clause [varPat () "a"] [] ((varExpr () "a"))
    ]) (nameSupply "$")

testExpr32 = evalSupply (compilePatterns [varExpr () "x"] 
    [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True))
    , Clause [conPat () "[]" []] [] (litExpr () (TBool False))
    ]) (nameSupply "$")


testExpr33 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr33 = 
    patExpr () [litExpr () (TInt 2)]
        [ Clause [ asPat () "x" (orPat () (litPat () (TInt 1)) (litPat () (TInt 2))) ] [] (varExpr () "x") ]

testExpr34 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr34 = 
    patExpr () [litExpr () (TInt 1)]
        [ Clause [ asPat () "x" (litPat () (TInt 1)) ] [] (varExpr () "x") 
        , Clause [ asPat () "x" (litPat () (TInt 2)) ] [] (varExpr () "x") ]

testExpr34b :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr34b = 
    lamExpr () [varPat () "z"] (patExpr () [varExpr () "z"]
        [ Clause [ asPat () "x" (litPat () (TInt 1)) ] [] (varExpr () "x") 
        , Clause [ asPat () "x" (litPat () (TInt 2)) ] [] (varExpr () "x") 
        , Clause [ anyPat () ] [] (litExpr () (TInt 100)) 
        ])


testExpr35 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr35 = 
    patExpr () [litExpr () (TInt 1)] [ Clause [ asPat () "x" (litPat () (TInt 1)) ] [] (varExpr () "x") ]

testExpr36 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr36 =
    patExpr () [] [Clause [lstPat () [orPat () (litPat () (TInt 1)) (litPat () (TInt 2))]] [] (litExpr () (TInt 1))]

testExpr37 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr37 =
    appExpr () [varExpr () "(>=)", litExpr () (TInt 5), litExpr () (TInt 5)]

testExpr38 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr38 =
    fixExpr () "fixS" (lamExpr () [varPat () "f", varPat () "s"] (patExpr () [] 
        [ Clause [conPat () "Z" []] [] (varExpr () "s")
        , Clause [asPat () "nat" (conPat () "S" [varPat () "n"])] [] (appExpr () [varExpr () "fixS", varExpr () "f", appExpr () [varExpr () "f", varExpr () "nat", varExpr () "s"], varExpr () "n"])
        ])) (varExpr () "fixS")

testExpr39 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr39 =
    letExpr () (BLet (varPat () "x")) (conExpr () "S" [conExpr () "S" [conExpr () "S" [conExpr () "Z" []]]])
        (fixExpr () "fixS" (lamExpr () [varPat () "f", varPat () "s"] (patExpr () [] 
            [ Clause [conPat () "Z" []] [] (varExpr () "s")
            , Clause [asPat () "nat" (conPat () "S" [varPat () "n"])] [] (appExpr () [varExpr () "fixS", varExpr () "f", appExpr () [varExpr () "f", varExpr () "nat", varExpr () "s"], varExpr () "n"])
            ])) (appExpr () [varExpr () "fixS", lamExpr () [anyPat (), varPat () "z"] (op2Expr () (OAdd ()) (varExpr () "z") (litExpr () (TInt 1))), litExpr () (TInt 0), varExpr () "x"]))

testExpr40 :: Expr () (Pattern () () ()) (Binding (Pattern () () ())) [Pattern () () ()] (Op1 ()) (Op2 ()) c d
testExpr40 =
    letExpr () (BLet (varPat () "x")) (conExpr () "S" [conExpr () "S" [conExpr () "S" [conExpr () "Z" []]]])
        (fixExpr () "fixS" (lamExpr () [varPat () "f", varPat () "s"] (patExpr () [] 
            [ Clause [conPat () "Z" []] [] (varExpr () "s")
            , Clause [asPat () "nat" (conPat () "S" [varPat () "n"])] [] (appExpr () [varExpr () "fixS", varExpr () "f", appExpr () [varExpr () "f", varExpr () "nat", varExpr () "s"], varExpr () "n"])
            ])) (appExpr () [varExpr () "fixS", lamExpr () [varPat () "x", varPat () "a"] (undefined), litExpr () (TInt 0), varExpr () "x"]))

testModule41 =
    Module
      { moduleName = "Test"
      , moduleTypes = 
          [ Sum "Nat" [] 
              [ Prod "Z" []
              , Prod "S" [ typ "Nat" ] 
              ] 
          ]
      , moduleDefs = 
          [ Def "foldS" 
              [ Clause [] [] undefined ] 
              []
          , Def "foldCons" 
              [ Clause [] [] undefined ] 
              []
          , Def "toNat" 
              [ Clause [] [] undefined ] 
              []
          , Def "fromNat" 
              [ Clause [] [] undefined ] 
              []
          , Def "factorial" 
              [ Clause [] [] undefined ] 
              []
          , Def "id" 
              [ Clause [varPat () "x"] [] (varExpr () "x") ] 
              []
          , Def "withDefault" 
              [ Clause [] [] undefined ] 
              [ Def "notZero"
                  []
                  []
              , Def "baz"
                  []
                  []
              ]
          , Def "map" 
              [ Clause [] [] undefined ] 
              []
          , Def "myList" 
              [ Clause [] [] undefined ] 
              []
          , Def "main" 
              [ Clause [] [] undefined ] 
              []
          ]
      , moduleClasses = 
          []
      , moduleInstances = 
          []
      }

testModule42 =
    Module
      { moduleName = "Test"
      , moduleTypes = 
          [ Sum "Nat" [] 
              [ Prod "Z" []
              , Prod "S" [ typ "Nat" ] 
              ] 
          , Sum "List" ["a"] 
              [ Prod "Nil" []
              , Prod "Cons" [ tVar kTyp "a", tList (tVar kTyp "a") ] 
              ] 
          ]
      , moduleDefs = 
          [ Def "id" 
              [ Clause [varPat () "x"] [] (varExpr () "x") ] 
              []
          , Def "myFun" 
              [ Clause [varPat () "n"] [] (conExpr () "S" [varExpr () "n"]) ] 
              []
          ]
      , moduleClasses = 
          []
      , moduleInstances = 
          []
      }

testType43 =
    runInfer classEnv typeEnv (generalize (tVar kTyp "a" `tArr` tList (tVar kTyp "a") `tArr` tList (tVar kTyp "a")))

testType44 = Sum "List" ["a"] 
              [ Prod "Nil" []
              , Prod "Cons" [ tVar kTyp "a", tList (tVar kTyp "a") ] 
              ] 

testType45 = Sum "List" [] 
              [ Prod "Nil" []
              , Prod "Cons" [ tVar kTyp "a", tList (tVar kTyp "a") ] 
              ] 

testDef46 = Def "id" [ Clause [varPat () "x"] [] (varExpr () "x") ] []

--testTypeClassDef47 = 
--    ( [InClass "Show" (tVar kTyp "a")]
--    , "ToString"
--    , tVar kTyp "a"
--    , [("toString", tVar kTyp "a" `tArr` tString)]
--    )

--xx = 
--    ( InClass "Show" "a"
--    , InClass "ToString" "a"
--    , [("toString", tVar kTyp "a" `tArr` tString)]
--    )
--
--yy = 
--    ( InClass "Show" tInt
--    , InClass "ToString" tInt
--    , [("toString", varExpr () "@Int.show")]
--    )

--testTypeClassDef47 :: ClassDef
testTypeClassDef47 = 
    ( [InClass "Show" "a"]
    , InClass "ToString" "a"
    , [("toString", tVar kTyp "a" `tArr` tString)]
    )

--testInstance48 :: Instance2
testInstance48 = 
    ( []
    , InClass "ToString" tInt
    , [("toString", varExpr () "@Int.show")]
    )

testX = 
    case runTest testExpr39 of 
        Left e -> error e
        Right (r, q , c, z) -> do
            putStrLn (showTree (nodesToString (prettyAst r)))
            putStrLn (showTree (nodesToString (prettyAst q)))
            putStrLn "Core ::"
            putStrLn (showTree (nodesToString (prettyCoreTree c)))
            putStrLn (show z)

--runTest :: Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] (Op1 t) (Op2 t) -> m (Ast NodeInfo Void Void)
runTest expr = do
    ((ast, ast2), (sub, _)) <- runInfer classEnv typeEnv (do
        ast <- infer expr
        sub <- gets fst
        let ast1 = astApply sub ast
        foo <- evalStateT (compileClasses (desugarOperators ast1)) [] 
        pure (ast1 :: Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) () () () (), foo)
        )

    let (c, z) = 
            case evalSupply (compileExpr (extractType ast2)) (numSupply "$") of
                Just c -> (c, evalExpr c evalEnv)
                Nothing -> error "==fail=="

    pure (ast, ast2, c, z)



compileExpr2
  :: (MonadState (Substitution, Context) m, MonadError String m, MonadSupply Name m, MonadReader (ClassEnv f g c d, TypeEnv) m)
  => Expr t (Pattern t f g) (Binding (Pattern t f g)) [Pattern t f g] (Op1 t) (Op2 t) c d
  -> m Core
compileExpr2 e = do
    ast <- infer e
    sub <- gets fst
    let ast2 = astApply sub ast
    ast4 <- evalStateT (compileClasses (desugarOperators ast2)) []
    compileExpr (extractType ast4)
--    cc <- expandFunPats (extractType ast4) -- (mapTags nodeType ast4)
--    dd <- unrollLets cc
--    ee <- simplify dd
--    toCore ee

--astVars :: (Free t) => Ast t n o -> [Name]
--astVars = nub . cata alg 
--  where 
--    alg = \case
--        EVar t _                -> free t
--        ECon t _ a              -> free t <> concat a
--        ELit t _                -> free t
--        EApp t a                -> free t <> concat a
--        ELet t _ a b            -> free t <> a <> b
--        EFix t _ a b            -> free t <> a <> b
--        EPat t a cs             -> free t <> concatMap (\(Clause _ a b) -> concat a <> b) cs
--        ELam t _ a              -> free t <> a
--        EIf  t a b c            -> free t <> a <> b <> c
--        EOp1 t _ a              -> free t <> a
--        EOp2 t _ a b            -> free t <> a <> b
--        EDot t _ a              -> free t <> a
--        ERec t (FieldSet fs)    -> free t <> concatMap (\(Field t _ a) -> free t <> a) fs
--        ETup t a                -> free t <> concat a
----    mapPatternTags f = cata $ \case
----        PVar t a            -> undefined
----        PCon t a b          -> undefined
----        PLit t a            -> undefined
----        PAny t              -> undefined
----        PAs  t a b          -> undefined
----        POr  t a b          -> undefined
----        PRec t (FieldSet fs) -> undefined
--
--test11 =
--    runInfer mempty mempty xx 
--  where
--    xx = generalize ((tTuple [tVar kTyp "a1", tVar kTyp "a1"] `tArr` tInt) :: Type)
--    runInfer e1 e2 = 
--        --flip runStateT (mempty, Env.fromList [("a1", [InClass "Show" (tVar kTyp "a1")])])
--        flip runStateT (mempty, Env.fromList [("a1", Set.fromList ["Show"])])
--            >>> flip runReaderT (e1, e2)
--            >>> flip evalSupplyT (numSupply "a")
--            >>> runExceptT
--            >>> fromMaybe (Left "error")
--
--
----test15 = 
----    runInfer classEnv mempty xx 
----  where
----    xx = xxxyyy "a1" (tTuple [tUnit, tInt])
----    runInfer e1 e2 = 
----        --flip runStateT (mempty, Env.fromList [("a1", [InClass "Show" (tVar kTyp "a1")])])
----        flip runStateT (mempty, Env.fromList [("a1", Set.fromList ["Show"])])
----            >>> flip runReaderT (e1, e2)
----            >>> flip evalSupplyT (numSupply "a")
----            >>> runExceptT
----            >>> fromMaybe (Left "error")
--
--
--test16 = 
--    runInfer classEnv mempty xx 
--  where
--    xx = instantiate (Forall [kTyp] [InClass "Show" 0] (tArr (tGen 0) tInt))
--    runInfer e1 e2 = 
--        -- flip runStateT (mempty, Env.fromList [("a1", [InClass "Show" (tVar kTyp "a1")])])
--        flip runStateT (mempty, Env.fromList [("a1", Set.fromList ["Show"])])
--            >>> flip runReaderT (e1, e2)
--            >>> flip evalSupplyT (numSupply "a")
--            >>> runExceptT
--            >>> fromMaybe (Left "error")
--
--
--test17 = 
--    runInfer classEnv mempty xx 
--  where
--    xx = generalize (tVar kTyp "a1" `tArr` tVar kTyp "a2" `tArr` tInt)
--    runInfer e1 e2 = 
--        -- flip runStateT (mempty, Env.fromList [("a1", [InClass "Show" (tVar kTyp "a1")])])
--        flip runStateT (mempty, Env.fromList [("a1", Set.fromList ["Show"])])
--            >>> flip runReaderT (e1, e2)
--            >>> flip evalSupplyT (numSupply "a")
--            >>> runExceptT
--            >>> fromMaybe (Left "error")
--
--
--
--
--

main = print "Hello"

--classEnv :: ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) f)
classEnv = Env.fromList 
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
    , ( "Eq"
      , ( ( []
          , InClass "Eq" "a"
          , [ ("(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool) ]
          )
          -- Instances
        , [ ( []
            , InClass "Eq" tInt
            , [ ("(==)", varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)")
              ]
            )
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
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) (fieldSet [
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
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tInt) []) (fieldSet [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@Int.show")]))
--          --, Instance [] tBool (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [])  (fieldSet [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")]))
----          , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tList (tVar kTyp "a"))) []) (fieldSet [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11]))
--          , Instance [InClass "Show" (tVar kTyp "a"), InClass "Show" (tVar kTyp "b")] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) (fieldSet [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_]))
--          ]
--        )
--      )
--    , ( "Eq"
--      , ( []
--        , "a"
--        , []
----        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Eq") tInt) []) (fieldSet [ Field (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "(==)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)") ] ))
--        , [ ]
--        )
--      )
--    , ( "Ord"
--      , ( ["Eq"]
--        , "a"
--        , []
--        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Ord") tInt) []) (fieldSet 
--              [ Field (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "(>)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)") 
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) "(>=)" gte_
--              ] ))
--          ]
--        )
--      )
--    ]
  where
    gte_ = lamExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) []) [varPat (NodeInfo tInt []) "a", varPat (NodeInfo tInt []) "b"] 
              (appExpr (NodeInfo tBool []) [varExpr (NodeInfo (tInt `tArr` tInt `tArr` tBool) [InClass "Eq" tInt]) "(==)", varExpr (NodeInfo tInt []) "a", varExpr (NodeInfo tInt []) "b"])

    foo11 = varExpr (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "showList"
    showPair_ = lamExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) [varPat (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"] (appExpr (NodeInfo tString []) [varExpr (NodeInfo (tString `tArr` tString `tArr` tString `tArr` tString) []) "@strconcat3", appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "a" `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "show", (appExpr (NodeInfo (tVar kTyp "a") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "a") []) "first", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"])], litExpr (NodeInfo tString []) (TString ","), appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "b" `tArr` tString) [InClass "Show" (tVar kTyp "b")]) "show", appExpr (NodeInfo (tVar kTyp "b") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "b") []) "second", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"]]])

typeEnv = Env.fromList 
    [ ( "(==)" , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool) )
    , ( "(>=)" , Forall [kTyp] [InClass "Ord" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool) )
    , ( "(+)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(-)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
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

    , ( "@Int.(+)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(-)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )
    , ( "@Int.(*)" , Forall [] [] (tInt `tArr` tInt `tArr` tInt) )

    , ( "lenShow"  , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` tInt) ) 

    , ( "Z"  , Forall [] [] (tCon kTyp "Nat") ) 
    , ( "S"  , Forall [] [] (tCon kTyp "Nat" `tArr` tCon kTyp "Nat") ) 
    ]


data N = Z | S N

data L = H | C Int L


recN f s Z = s
recN f s (S a) = recN f (f (S a) s) a 

recN_ f s Z = s
recN_ f s (S a) = recN_ f (f s) a 

test992 = recN (\_ (_, x:xs) -> (Just x, xs)) (Nothing, [1,2,3,4,5,6,7]) (S (S (S (S Z)))) 

--nth n xs =
--  reduce Succ init 0
--    | (_, x :: xs) => (Some x, xs)
--    | (_, _)       => (None, ????)

--test992b = rec (\_ (_, x:xs) -> (Just x, xs)) (S (S (S (S Z)))) (Nothing, [1,2])

test993 = recN go 0 (S (S (S (S Z)))) 
  where
    go _ s = s + 1

fromNat = recN_ go 0 where go s = s + 1

-- length = 
--   reduce Cons init 0 
--     | s => s + 1

-- length = 
--   Cons.reduce 
--     = 0 
--     | s => s + 1 

-- length = rec Cons 


recC f H s = s
recC f (C n a) s = recC f a (f n (C n a) s)

test994 = recC (\_ _ s -> s + 1) (C 0 (C 1 (C 2 H))) 0


--test994 = recursive C 0 | _ _ s => s + 1

test995 = recC (\x _ s y -> s (x:y)) (C 0 (C 1 (C 2 H))) id []


testmap f = recC (\x _ s y -> s (f x:y)) (C 0 (C 1 (C 2 H))) id []


testfact = recN go 1 (S (S (S (S (S Z)))))
  where
    go x a = fromNat x * a

-- fact = 
--   reduce Succ init 1 | a => fromNat elem * a

--class B b where
--    what :: b -> String
--
----instance B Int where
----    what = show
--
--class B a => A a where
--    doStuff :: a -> String
--
--instance A Int where
--    doStuff = what
--
---- type Nat = Zero | Succ Nat
