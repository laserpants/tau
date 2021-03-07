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
import Control.Monad.Writer
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
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution (Substitution, apply)
import Tau.Comp.Type.Unification
import Tau.Eval.Core
import Tau.Eval.Repl
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Pretty.Ast
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
--                    [ Clause [litPat () (LInt 5)] [] (litExpr () (LInt 1))
--                    , Clause [varPat () "y"] [] (litExpr () (LInt 2)) ])
--            , litExpr () (LInt 5) ]
--
--test22 = case test2 of
--    Just c -> do
--        traceShowM c
--        evalExpr c mempty
--
--test3 = evalSupply (compileExpr e) (numSupply "$")
--  where 
--    e = patExpr () [litExpr () (LInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (LInt 9), conExpr () "[]" []]]
--        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "ys")
--        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (litExpr () (LString "e2"))
--        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (litExpr () (LString "e3"))
--        ]
--
--test33 = case test3 of
--    Just c -> do
--        traceShowM c
--        evalExpr c evalEnv

evalEnv = Env.fromList 
    [ ("(::)"    , constructor "(::)" 2)  
    , ("[]"      , constructor "[]"   0)  
    , ("Some"    , constructor "Some" 1)  
    , ("None"    , constructor "None" 0)  
    , ("{show}"  , constructor "{show}" 1)  
    , ("{(*),(+),(-)}" , constructor "{(*),(+),(-)}" 3)  
    , ("(,)"     , constructor "(,)" 2)  
    , ("show"    , fromJust (evalExpr show_ mempty))
    , ("lenShow" , fromJust (evalExpr lenShow mempty))
    , ("first"   , fromJust (runEval (eval fst_) mempty))
    , ("second"  , fromJust (runEval (eval snd_) mempty))
    , ("(+)"     , fromJust (evalExpr plus__ mempty))
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
 

---- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
--test4 = evalSupply (compileExpr e) (numSupply "$")
--  where 
--    e = letExpr () (BLet (varPat () "f")) (patExpr () [] 
--        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
--        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
--      ]) (appExpr () [varExpr () "f", litExpr () (LInt 5)]) 
--
----    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]])
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
--        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
--        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
--      ]) (appExpr () [varExpr () "f", litExpr () (LInt 10)]) 
--
----    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]])
--
--test55 = case test5 of
--    Just c -> do
--        traceShowM c
--        evalExpr c evalEnv
--
--
--
--type Infer a = StateT (Substitution, Context) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv c -> TypeEnv -> StateT (Substitution, Context) (ReaderT (ClassEnv c, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a -> Either String (a, (Substitution, Context))
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
----                    [ Clause [litPat () (LInt 5)] [] (litExpr () (LInt 1))
----                    , Clause [varPat () "y"] [] (litExpr () (LInt 2)) ])
----            , litExpr () (LInt 5) ]
--
--    -- match 5 [] (9 :: []) with
--    --   | f []        ys        => ys
--    --   | f (x :: xs) []        => e2
--    --   | f (x :: xs) (y :: ys) => ys
--    -- 
--    e = patExpr () [litExpr () (LInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (LInt 9), conExpr () "[]" []]]
--        [ Clause [varPat () "f" , conPat () "[]" []                                , varPat () "ys"] 
--              [op2Expr () (OEq ()) (litExpr () (LInt 5)) (litExpr () (LInt 8))]    
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
--        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
--        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
--      ]) (appExpr () [varExpr () "f", litExpr () (LInt 5)]) 
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
--    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
--    --e = letExpr () (BFun "baz" [varPat () "x"]) (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)]) (dotExpr () "baz" (litExpr () (LInt 5)))
--    --e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)])) (dotExpr () "baz" (litExpr () (LInt 5)))
----    e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)])) (appExpr () [varExpr () "baz", litExpr () (LInt 5)])
----    e = letExpr () (BFun "g" [varPat () "x", conPat () "Some" [varPat () "y"]]) (lamExpr () [varPat () "z"] (varExpr () "z"))
----        (appExpr () [varExpr () "g", litExpr () (LInt 1), conExpr () "Some" [litExpr () (LInt 5)], litExpr () LUnit])
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
----    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
----    e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)])) (appExpr () [varExpr () "baz", litExpr () (LInt 5)])
----    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
--
----    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
-- 
--    e = letExpr () (BFun "baz" [varPat () "x"]) (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)]) (dotExpr () "baz" (litExpr () (LInt 5)))
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
--        , conExpr () "Some" [litExpr () (LInt 5)]
--        , conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]
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
--        , conExpr () "Some" [litExpr () (LInt 5)]
--        , conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]
--        ]

testExpr2 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr2 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")

testExpr3 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr3 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])

testExpr4 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr4 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])

testExpr5 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr5 = lamExpr () [varPat () "x"] (letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))

testExpr6 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr6 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))

testExpr7 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr7 = appExpr () [varExpr () "lenShow", litExpr () (LInt 12345)]

testExpr8 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr8 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])

testExpr9 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr9 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")

-- let f x = lenShow in f ()
testExpr10 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr10 = letExpr () (BFun "f" [varPat () "x"]) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () LUnit])

-- let p = (5, 1) in show p
testExpr11 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr11 = letExpr () (BLet (varPat () "p")) (conExpr () "(,)" [litExpr () (LInt 5), litExpr () (LInt 1)]) (appExpr () [varExpr () "show", varExpr () "p"])

-- \x => show (x, x)
testExpr12 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr12 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", conExpr () "(,)" [varExpr () "x", varExpr () "x"]])

--testExpr21 = op2Expr () OAdd (litExpr () (LFloat 3.1)) (litExpr () (LFloat 4.1)) 
testExpr21 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr21 = op2Expr () (OAdd ()) (litExpr () (LInt 3)) (litExpr () (LInt 4)) 

testExpr22 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr22 = appExpr () [patExpr () [] [
      Clause [ conPat () "(::)" [litPat () (LInt 2), varPat () "z"]
             , varPat () "y" ] [] (litExpr () (LString "one")) 
    , Clause [ varPat () "x"       
             , litPat () (LInt 4) ] [] (litExpr () (LString "two")) 
    , Clause [ conPat () "(::)" [anyPat (), anyPat ()]
             , varPat () "x" ] [] (litExpr () (LString "three"))
    ], conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []], litExpr () (LInt 4)]

testExpr23 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr23 = appExpr () [letExpr () (BFun "f" [varPat () "x"]) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () LUnit]), litExpr () (LInt 873)] 

testExpr24 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
testExpr24 = appExpr () [lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", conExpr () "(,)" [varExpr () "x", varExpr () "x"]]), litExpr () (LInt 11)]

testX = 
    case runTest testExpr21 of 
        Left e -> error e
        Right (r, q , c, z) -> do
            putStrLn (showTree (nodesToString (prettyAst r)))
            putStrLn (showTree (nodesToString (prettyAst q)))
            putStrLn (showTree (nodesToString (prettyCore c)))
            putStrLn (show z)

--runTest :: Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] (Op1 t) (Op2 t) -> m (Ast NodeInfo Void Void)
runTest expr = do
    ((ast, ast2), (sub, _)) <- runInfer classEnv typeEnv (do
        ast <- infer expr
        sub <- gets fst
        let ast1 = astApply sub ast
        foo <- evalStateT (compileClasses (desugarOperators ast1)) [] 
        pure (ast1 :: Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo), foo)
        )

    let (c, z) = 
            case evalSupply (compileExpr (extractType ast2)) (numSupply "$") of
                Just c -> (c, evalExpr c evalEnv)
                Nothing -> error "==fail=="

    pure (ast, ast2, c, z)



astApply :: Substitution -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) -> Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo) 
astApply sub = mapTags (apply sub :: NodeInfo -> NodeInfo)

extractType :: Ast NodeInfo Void Void -> Ast Type Void Void
extractType = (mapTags :: (NodeInfo -> Type) -> Ast NodeInfo Void Void -> Ast Type Void Void) nodeType

compileExpr2
  :: (MonadState (Substitution, Context) m, MonadError String m, MonadSupply Name m, MonadReader (ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo)), TypeEnv) m)
  => Expr t (Pattern t) (Binding (Pattern t)) [Pattern t] (Op1 t) (Op2 t)
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

classEnv :: ClassEnv (Ast NodeInfo (Op1 NodeInfo) (Op2 NodeInfo))
classEnv = Env.fromList 
    [ ( "Num"
      , ( []
        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) (fieldSet [
              Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)")
              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)")
              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)")
            ]))
--              [ Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(+)Int")
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(*)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(*)Int")
--              , Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(-)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(-)Int")
--              ])
          ] 
        )
      )
    , ( "Show"
      , ( []
        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tInt) []) (fieldSet [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@Int.show")]))
          --, Instance [] tBool (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [])  (fieldSet [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")]))
--          , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tList (tVar kTyp "a"))) []) (fieldSet [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11]))
          , Instance [InClass "Show" (tVar kTyp "a"), InClass "Show" (tVar kTyp "b")] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) (fieldSet [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_]))
          ]
        )
      )
    ]
  where
    foo11 = varExpr (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "showList"
    showPair_ = lamExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) [varPat (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"] (appExpr (NodeInfo tString []) [varExpr (NodeInfo (tString `tArr` tString `tArr` tString `tArr` tString) []) "@strconcat3", appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "a" `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "show", (appExpr (NodeInfo (tVar kTyp "a") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "a") []) "first", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"])], litExpr (NodeInfo tString []) (LString ","), appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "b" `tArr` tString) [InClass "Show" (tVar kTyp "b")]) "show", appExpr (NodeInfo (tVar kTyp "b") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "b") []) "second", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"]]])

typeEnv = Env.fromList 
    [ ( "(==)" , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
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

    , ( "lenShow"  , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
    ]

