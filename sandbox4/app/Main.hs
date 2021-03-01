{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply 
import Control.Monad.Writer
import Data.Maybe
import Data.Text (Text)
import Data.Tree.View (showTree)
import Tau.Comp.Core
import Tau.Comp.Type.Inference
import Tau.Comp.Type.Substitution
import Tau.Comp.Type.Unification
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Pretty.Ast
import Tau.Lang.Type
import Tau.Util
import Tau.Util.Env (Env(..))
import qualified Tau.Util.Env as Env

noDups = undefined

mapPairs :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs =
    matchAlgo
        [varExpr () "u1", varExpr () "u2", varExpr () "u3"] 
        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "e1")
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (varExpr () "e2")
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
        ]
        (varExpr () "FAIL")

mapPairs2 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs2 =
    matchAlgo
        [varExpr () "u2", varExpr () "u3"] [ Clause [conPat () "[]" [], varPat () "ys"] [] (varExpr () "e1")
        , Clause [conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (varExpr () "e2")
        , Clause [conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
        ]
        (varExpr () "FAIL")

mapPairs3 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs3 =
    matchAlgo
        [varExpr () "u2"] 
        [ Clause [conPat () "[]" []] [] (varExpr () "e1")
--        , Clause [varPat () "x", varPat () "xs", conPat () "[]" []] [] (varExpr () "e2")
--        , Clause [varPat () "x", varPat () "xs", conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "e3")
        ]
        (varExpr () "FAIL")


mapPairs4 :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
mapPairs4 =
    matchAlgo
        [] 
        [ Clause [] [] (varExpr () "e2")
        ]
        (varExpr () "FAIL")



test1 = evalSupply mapPairs (numSupply "$")


test2 = evalSupply (pipeline e) (numSupply "$")
  where
    e = appExpr ()
            [ lamExpr () [varPat () "x"]
                (patExpr () [varExpr () "x"]
                    [ Clause [litPat () (LInt 5)] [] (litExpr () (LInt 1))
                    , Clause [varPat () "y"] [] (litExpr () (LInt 2)) ])
            , litExpr () (LInt 5) ]

test22 = case test2 of
    Just c -> do
        traceShowM c
        evalExpr c mempty

test3 = evalSupply (pipeline e) (numSupply "$")
  where 
    e = patExpr () [litExpr () (LInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (LInt 9), conExpr () "[]" []]]
        [ Clause [varPat () "f", conPat () "[]" [], varPat () "ys"] [] (varExpr () "ys")
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "[]" []] [] (litExpr () (LString "e2"))
        , Clause [varPat () "f", conPat () "(::)" [varPat () "x", varPat () "xs"], conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (litExpr () (LString "e3"))
        ]

test33 = case test3 of
    Just c -> do
        traceShowM c
        evalExpr c evalEnv

evalEnv = Env.fromList 
    [ ("(::)"   , constructor "(::)" 2)  
    , ("[]"     , constructor "[]"   0)  
    , ("Some"   , constructor "Some" 1)  
    , ("None"   , constructor "None" 0)  
    ]
 

-- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
test4 = evalSupply (pipeline e) (numSupply "$")
  where 
    e = letExpr () (BLet (varPat () "f")) (patExpr () [] 
        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
      ]) (appExpr () [varExpr () "f", litExpr () (LInt 5)]) 

--    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]])

test44 = case test4 of
    Just c -> do
        traceShowM c
        evalExpr c evalEnv


-- fix f = fun | 0 => 1 | n => n * f (n - 1) in f 5
test5 = evalSupply (pipeline e) (numSupply "$")
  where 
    e = fixExpr () "f" (patExpr () [] 
        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
      ]) (appExpr () [varExpr () "f", litExpr () (LInt 10)]) 

--    (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]])

test55 = case test5 of
    Just c -> do
        traceShowM c
        evalExpr c evalEnv



type Infer a = StateT (Substitution, Env [Predicate]) (ReaderT (ClassEnv a, TypeEnv) (SupplyT Name (ExceptT String Maybe))) a 

runInfer :: ClassEnv a -> TypeEnv -> Infer a -> Either String (a, (Substitution, Env [Predicate]))
runInfer e1 e2 = 
    flip runStateT (mempty, mempty)
        >>> flip runReaderT (e1, e2)
        >>> flip evalSupplyT (numSupply "a")
        >>> runExceptT
        >>> fromMaybe (Left "error")

test6 =
    runInfer classEnv typeEnv f
  where
    f :: Infer (Ast NodeInfo)
    f = infer e
--    e = appExpr ()
--            [ lamExpr () [varPat () "x"]
--                (patExpr () [varExpr () "x"]
--                    [ Clause [litPat () (LInt 5)] [] (litExpr () (LInt 1))
--                    , Clause [varPat () "y"] [] (litExpr () (LInt 2)) ])
--            , litExpr () (LInt 5) ]

    -- match 5 [] (9 :: []) with
    --   | f []        ys        => ys
    --   | f (x :: xs) []        => e2
    --   | f (x :: xs) (y :: ys) => ys
    -- 
    e = patExpr () [litExpr () (LInt 5), conExpr () "[]" [], conExpr () "(::)" [litExpr () (LInt 9), conExpr () "[]" []]]
        [ Clause [varPat () "f" , conPat () "[]" []                                , varPat () "ys"] 
              [op2Expr () OEq (litExpr () (LInt 5)) (litExpr () (LInt 8))]    
              (varExpr () "ys")
        , Clause [varPat () "f" , conPat () "(::)" [varPat () "x", varPat () "xs"] , conPat () "[]" []] [] 
              (conExpr () "[]" [])
        , Clause [varPat () "f" , conPat () "(::)" [varPat () "x", varPat () "xs"] , conPat () "(::)" [varPat () "y", varPat () "ys"]] [] 
              (varExpr () "ys")
        ]


test66 = let Right (ast, (sub, _)) = test6 in putStrLn (showTree (nodesToString (prettyAst (mapExprTags (apply sub) (mapExprTags nodeType ast)))))


test7 =
    runInfer classEnv typeEnv f
  where
    f :: Infer (Ast NodeInfo)
    f = infer e
    e = fixExpr () "f" (patExpr () [] 
        [ Clause [litPat () (LInt 0)] [] (litExpr () (LInt 1))
        , Clause [varPat () "n"] [] (appExpr () [varExpr () "@Int.(*)", varExpr () "n", appExpr () [varExpr () "f", appExpr () [varExpr () "@Int.(-)", varExpr () "n", litExpr () (LInt 1)]]])
      ]) (appExpr () [varExpr () "f", litExpr () (LInt 5)]) 

test77 = 
    case test7 of
        Left e -> error e
        Right (ast, (sub, _)) -> 
            putStrLn (showTree (nodesToString (prettyAst (mapExprTags (apply sub) (mapExprTags nodeType ast)))))


--test1 = runSupply e (numSupply "$")
--  where
--    e :: (MonadSupply Name m) => m (Expr () (Prep ()) Name Name)
--    e = pipeline mapPairs


test8 =
    runInfer classEnv typeEnv f
  where
    f :: Infer (Ast NodeInfo)
    f = infer e
    -- let g x (Some y) = \z => z in g (Some 5) ()
    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
    --e = letExpr () (BFun "baz" [varPat () "x"]) (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)]) (dotExpr () "baz" (litExpr () (LInt 5)))
    --e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)])) (dotExpr () "baz" (litExpr () (LInt 5)))
--    e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)])) (appExpr () [varExpr () "baz", litExpr () (LInt 5)])
--    e = letExpr () (BFun "g" [varPat () "x", conPat () "Some" [varPat () "y"]]) (lamExpr () [varPat () "z"] (varExpr () "z"))
--        (appExpr () [varExpr () "g", litExpr () (LInt 1), conExpr () "Some" [litExpr () (LInt 5)], litExpr () LUnit])
         

test88 = 
    case test8 of
        Left e -> error e
        Right (ast, (sub, _)) -> do
            traceShowM ast
            traceShowM "^^^^^^^^^^^^^^"
            traceShowM (mapExprTags nodeType ast)
            traceShowM "^^^^^^^^^^^^^^"
            traceShowM (mapExprTags (apply sub) (mapExprTags nodeType ast))
            traceShowM "^^^^^^^^^^^^^^"
            traceShowM "^^^^^^^^^^^^^^"
            putStrLn (showTree (nodesToString (prettyAst (mapExprTags (apply sub) (mapExprTags nodeType ast)))))


test888 = 
    case evalSupply (pipeline e) (numSupply "$") of
        Just c -> evalExpr c evalEnv
  where
--    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
--    e = letExpr () (BLet (varPat () "baz")) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)])) (appExpr () [varExpr () "baz", litExpr () (LInt 5)])
--    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))

--    e = letExpr () (BFun "baz" [varPat () "x"]) (op2Expr () OAdd (varExpr () "x") (litExpr () (LInt 1))) (dotExpr () "baz" (litExpr () (LInt 5)))
 
    e = letExpr () (BFun "baz" [varPat () "x"]) (appExpr () [varExpr () "@Int.(+)", varExpr () "x", litExpr () (LInt 1)]) (dotExpr () "baz" (litExpr () (LInt 5)))


test9 =
    runInfer classEnv typeEnv f
  where
    f :: Infer (Ast NodeInfo)
    f = infer e
    -- let g x (Some y) = \z => z in g (Some 5) ()
    e = appExpr () 
        [ lamExpr () [conPat () "Some" [varPat () "s"], conPat () "(::)" [varPat () "x", varPat () "xs"]] (varExpr () "s")
        , conExpr () "Some" [litExpr () (LInt 5)]
        , conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]
        ]


test99 = 
    case test9 of
        Left e -> error e
        Right (ast, (sub, _)) -> 
            putStrLn (showTree (nodesToString (prettyAst (mapExprTags (apply sub) (mapExprTags nodeType ast)))))


test999 = 
    case evalSupply (pipeline e) (numSupply "$") of
        Just c -> evalExpr c evalEnv
  where
    e = appExpr () 
        [ lamExpr () [conPat () "Some" [varPat () "s"], conPat () "(::)" [varPat () "x", varPat () "xs"]] (varExpr () "s")
        , conExpr () "Some" [litExpr () (LInt 5)]
        , conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]
        ]


test10a = do
    let Right (r, q) = runTest testExpr9 
    putStrLn (showTree (nodesToString (prettyAst r)))
    putStrLn (showTree (nodesToString (prettyAst q)))
  where
    testExpr2 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")
    testExpr3 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
    testExpr4 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])
    testExpr5 = lamExpr () [varPat () "x"] (letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
    testExpr6 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))
    testExpr7 = appExpr () [varExpr () "lenShow", litExpr () (LInt 555)]
    testExpr8 = lamExpr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])
    testExpr9 = letExpr () (BLet (varPat () "f")) (varExpr () "lenShow") (varExpr () "f")
    runTest expr = do
        (ast, (sub, x)) <- runInfer classEnv typeEnv (infer expr)
        traceShowM sub
        traceShowM x
--        pure ast
        pure (ast, mapExprTags (apply sub) ast)

main = print "Hello"

classEnv = Env.fromList []

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

