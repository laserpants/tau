{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Arrow (second, first)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Control.Monad.Supply
import Data.Maybe (fromJust)
import Data.Void
import Tau.Comp.Patterns
import Tau.Eval
import Tau.Expr
import Tau.Pretty
import Tau.PrettyTree
import Tau.Env (Env)
import Tau.Prim
import Tau.Stuff
import Tau.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Tau.Env as Env


--bork :: Int -> [a]
--bork = cata alg where
--    alg :: Algebra NatF [a]
--    alg = undefined


--
--

expr1 :: PatternExpr ()
expr1 = letExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")
expr2 = letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
expr3 = lamExpr () (varPat () "x") (appExpr () [varExpr () "lenShow", varExpr () "x"])
expr4 = lamExpr () (varPat () "x") (letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
expr5 = letExpr () (varPat () "f") (varExpr () "lenShow") (lamExpr () (varPat () "x") (appExpr () [varExpr () "f", varExpr () "x"]))
expr6 = appExpr () [varExpr () "lenShow", litExpr () (LInt 555)]
expr7 = lamExpr () (varPat () "x") (appExpr () [varExpr () "f", varExpr () "x"])
expr8 = lamExpr () (varPat () "x") (lamExpr () (varPat () "y") (appExpr () [varExpr () "f", lamExpr () (varPat () "x") (lamExpr () (varPat () "y") (varExpr () "z"))]))
expr9 = lamExpr () (varPat () "x") (appExpr () [varExpr () "lenShow2", varExpr () "x"])
expr99 = appExpr () [lamExpr () (varPat () "f") (appExpr () [varExpr () "f", litExpr () (LInt 5)]), varExpr () "lenShow"]
expr20 = letExpr () (varPat () "id") (lamExpr () (varPat () "x") (varExpr () "x")) 
              (appExpr () [
                  varExpr () "(,)"
                , appExpr () [varExpr () "id", litExpr () (LInt 5)]
                , appExpr () [varExpr () "id", litExpr () (LBool True)]
              ])
expr21 = lamExpr () (varPat () "x") (letExpr () (varPat () "f") (lamExpr () (varPat () "y") (varExpr () "x")) (litExpr () (LInt 1)))
expr22 = lamExpr () (varPat () "x") (letExpr () (varPat () "f") (varExpr () "lenShow2") (appExpr () [varExpr () "f", varExpr () "x"]))
expr23 = recExpr () [Field () "name" (litExpr () (LString "Bob")), Field () "id" (litExpr () (LInt 11)), Field () "admin" (litExpr () (LBool True))]

expr24 :: PatternExpr ()
expr24 = matExpr () [conExpr () "Nil" [], litExpr () (LInt 11)] 
            [ Clause [ conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LInt 5) ] [ eqOp () (varExpr () "x") (litExpr () (LInt 1)) ] (litExpr () (LInt 499))
            , Clause [ conPat () "Nil"  [], anyPat () ] [] (litExpr () (LInt 500)) 
            , Clause [ anyPat (), anyPat () ] [] (litExpr () (LInt 508)) 
            ]

expr241 :: PatternExpr ()
expr241 = matExpr () [conExpr () "Cons" [litExpr () (LInt 1), conExpr () "Nil" []], litExpr () (LInt 5)] 
            [ Clause [ conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LInt 5) ] [ eqOp () (varExpr () "x") (litExpr () (LInt 1)) ] (litExpr () (LInt 499))
            , Clause [ conPat () "Nil"  [], anyPat () ] [] (litExpr () (LInt 500)) 
            , Clause [ anyPat (), anyPat () ] [] (litExpr () (LInt 508)) ]

expr2412 :: PatternExpr ()
expr2412 = matExpr () [conExpr () "Cons" [litExpr () (LInt 1), conExpr () "Nil" []]] 
            [ Clause [ conPat () "Cons" [varPat () "x", varPat () "xs"] ] [ eqOp () (varExpr () "x") (litExpr () (LInt 1)) ] (litExpr () (LInt 499))
            , Clause [ anyPat () ] [] (litExpr () (LInt 508)) ]

expr2413 :: PatternExpr ()
expr2413 = matExpr () [litExpr () (LInt 11), litExpr () (LInt 85)] 
            --[ Clause [ conPat () "Cons" [varPat () "x", varPat () "xs"], litPat () (LInt 5) ] [ eqOp () (varExpr () "x") (litExpr () (LInt 1)) ] (litExpr () (LInt 499))
            [ Clause [ litPat () (LInt 1), litPat () (LInt 5) ] [] (litExpr () (LInt 499))
            , Clause [ anyPat (), anyPat () ] [] (litExpr () (LInt 508)) ]


expr2411 :: PatternExpr ()
expr2411 = matExpr () [litExpr () (LInt 1)] 
            [ Clause [ varPat () "x" ] [ eqOp () (varExpr () "x") (litExpr () (LInt 1)) ] (litExpr () (LInt 499))
            , Clause [ anyPat () ] [] (litExpr () (LInt 508)) ]

expr25 = appExpr () [varExpr () "toString", litExpr () (LInt 5)]

expr26 = appExpr () [lamExpr () (varPat () "x") (appExpr () [varExpr () "toString", varExpr () "x"]), litExpr () (LInt 5)]

expr27 = matExpr () [recExpr () [Field () "a" (litExpr () (LInt 5))]] [Clause [recPat () [Field () "a" (varPat () "b")]] [] (varExpr () "b")]

expr28 = letExpr () 
            (varPat () "f") 
            (lamExpr () (varPat () "d") (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "toString" (varPat () "toString")]] [] (varExpr () "toString")]))
            (appExpr () [varExpr () "f", recExpr () [Field () "toString" (varExpr () "@showInt")], litExpr () (LInt 5)])

expr29 = letExpr () 
            (varPat () "f") (lamExpr () (varPat () "d") (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "show" (varPat () "show"), Field () "toString" (varPat () "toString")]] [] (letExpr () (varPat () "show") (varExpr () "@showInt") (varExpr () "toString"))]))
            (appExpr () [varExpr () "f", recExpr () [Field () "show" (varExpr () "@showInt"), Field () "toString" (varExpr () "show")], litExpr () (LInt 5)])


expr30 = varExpr () "toString"

expr31 = letExpr () (varPat () "f") (lamExpr () (recPat () [Field () "stuff" (varPat () "x")]) (varExpr () "x")) (appExpr () [varExpr () "f", recExpr () [Field () "stuff" (litExpr () (LInt 5))]])

expr32 = appExpr () [varExpr () "toString", litExpr () (LInt 5)]

expr33 = letExpr () (varPat () "toStringInt") (varExpr () "show") 
              (appExpr () 
                [ (lamExpr () (varPat () "d") (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "toString" (varPat () "toString")]] [] (varExpr () "toString")]))
                , (recExpr () [Field () "toString" (varExpr () "toStringInt")])
                , (litExpr () (LInt 5))
              ])

expr34 = letExpr () (varPat () "f") (varExpr () "show") (appExpr () [varExpr () "f", litExpr () (LInt 5)])

expr35 = letExpr () (varPat () "f") (varExpr () "show") (appExpr () [lamExpr () (varPat () "x") (varExpr () "f"), litExpr () LUnit, litExpr () (LInt 5)])


runTest1_ :: IO ()
runTest1_ = do
    let Right (tree, (sub, x)) = runTest1 
    debugTree tree
    debugTree (mapTags (apply sub) tree)
    debug (show x)
    debug (show (apply sub <$$> x))
    let pexpr = mapTags (apply sub) tree
--    let tree = rebuildTree pexpr
    debug (show sub)

--runTest1 = runInfer mempty typeEnv (infer expr2) where
--runTest1 = runInfer mempty typeEnv (infer expr4) where
--runTest1 = runInfer mempty typeEnv (infer expr5) where
runTest1 = runInfer mempty typeEnv (infer expr6) where
--runTest1 = runInfer mempty typeEnv (infer expr20) where
--runTest1 = runInfer mempty typeEnv (infer expr21) where
--runTest1 = runInfer mempty typeEnv (infer expr4) where
  typeEnv = Env.fromList 
        [ ( "lenShow" , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
        , ( "(,)"     , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1))))
        ]
--        [ ( "lenShow" , Forall [kTyp, kTyp] [InClass "Show" (tGen 0)] (tGen 0 `tArr` upgrade tInt) ) 
--        , ( "(,)"     , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1))))
--        ]

myTypeEnv :: Env Scheme
myTypeEnv = Env.fromList 
    [ ( "@strlen"  , Forall [] [] (upgrade  (tString `tArr` tInt)) )
    , ( "@showInt" , Forall [] [] (upgrade  (tInt `tArr` tString)) )
    , ( "lenShow"  , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
    , ( "lenShow2" , Forall [kTyp, kTyp] [InClass "Show" 0, InClass "Eq" 0] (tGen 0 `tArr` upgrade tInt) ) 
    , ( "(,)"      , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1))))
    , ( "Nil"      , Forall [kTyp] [] (tApp (upgrade tListCon) (tGen 0)) )
    , ( "Cons"     , Forall [kTyp] [] (tGen 0 `tArr` tApp (upgrade tListCon) (tGen 0) `tArr` tApp (upgrade tListCon) (tGen 0)) )
    , ( "(==)"     , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
    , ( "toString" , Forall [kTyp] [InClass "ToString" 0] (tGen 0 `tArr` upgrade tString) )
    , ( "show"     , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tString) )

--    [ -- ( "@strlen" , sScheme (tCon kStar "String" `tArr` tCon kStar "Int") )
--    , -- ( "show"    , sForall kStar ["Show"] (sScheme (tGen 0 `tArr` tCon kStar "String")) )
    ]

--type ClassEnv a = Env (Class a)
--type Class a = ([Name], [Instance a])

myClassEnv :: ClassEnv (PatternExpr Type)
myClassEnv = Env.fromList
    [ ( "Show"
      , ( []
         , [ Instance [] tInt  (recExpr (tApp (tCon (kArr kTyp kTyp) "Show") tInt)  [Field (tInt `tArr` tString) "show" (varExpr (tInt `tArr` tString) "@showInt")])
           , Instance [] tBool (recExpr (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [Field (tBool `tArr` tString) "show" (varExpr (tBool `tArr` tString) "@showBool")])
           , Instance [] tUnit (recExpr (tApp (tCon (kArr kTyp kTyp) "Show") tUnit) [Field (tUnit `tArr` tString) "show" (varExpr (tUnit `tArr` tString) "@showUnit")])
           ]
        )
      )
    , ( "ToString"
      , ( ["Show"]
        , [ Instance [] tInt (recExpr (tApp (tCon (kArr kTyp kTyp) "ToString") tInt) [Field (tInt `tArr` tString) "toString" (varExpr (tInt `tArr` tString) "show")])
          ] )
      )
--    , ( "Eq"
--      , ( []
--        , [] )
--      )
    ]

--pipeline
--  :: (MonadError String m, MonadSupply Name m, MonadReader (ClassEnv a, TypeEnv) m)
--  => PatternExpr t
----  -> m (PatternExpr NodeInfo, Environments)
--  -> m (Expr Type (Prep Type) Name)
pipeline e =  do
    (tree, (sub, xxx1)) <- runStateT (infer e) mempty

    debugTree tree
    debugTree (mapTags (apply sub) tree)
--    debug (show x)
--    debug (show (apply sub <$$> x))

    let tree2 = (mapTags (apply sub) tree) 

    let tree3 = (insertDicts xxx1 tree2)

    debugTree tree3
    
    --tree4 <- runReaderT (rebuildTree22 tree3) []
    (tree4, _) <- withReaderT (\(a,b) -> (a,b,[])) (runStateT (rebuildTree22 tree3) [])

    debugTree tree4

    --

    let zzz3 = simplified (mapTags nodeType tree4)
    --traceShowM zzz3
    let Right zzz1 = zzz3

    debugTree2 zzz1

    let boo = evalExpr zzz1 myEvalEnv
    let Just foo = boo

    traceShowM boo
    traceShowM foo
    traceShowM "===="

    pure ()
    -- >> Apply context reduction

----    let t = tree :: PatternExpr NodeInfo
--    y <- runStateT (runReaderT (rebuildTree (insertDicts xxx1 tree2)) False) 
--            (Environments { classEnv = myClassEnv, typeEnv = myTypeEnv })
--
--    let (pex, e) = y
--
--    debugTree pex
--    traceShowM "^^"
--
--    let Right zzz1 = simplified (mapTags nodeType pex)
--
--    debugTree2 zzz1
--    traceShowM "---"
--
--    let Just foo = evalExpr zzz1 myEvalEnv
--
--    traceShowM foo
--    traceShowM "==="
--
--    pure zzz1

myEvalEnv = Env.fromList 
    [ ("toString" , fromJust (runEval (eval toString) mempty))
    , ("show"     , fromJust (runEval (eval show_) mempty))
    , ("lenShow"  , fromJust (runEval (eval lenShow) mempty))
    , ("(,)"      , constructor "(,)" 2) -- fromJust (runEval (eval pair) mempty))
    , ("Nil"      , constructor "Nil" 0) -- fromJust (runEval (eval pair) mempty))
    , ("Cons"     , constructor "Cons" 2) -- fromJust (runEval (eval pair) mempty))
    ]
  where
    Right show_ = simplified foo2
    foo2 = lamExpr () (varPat () "d") (matExpr () [varExpr () "d"] [ Clause [recPat () [Field () "show" (varPat () "show")]] [] (varExpr () "show") ])

    Right toString = simplified foo
--  -- \d => match d with | { toString = toString } => toString 
    foo = lamExpr () (varPat () "d") (matExpr () [varExpr () "d"] 
          [ Clause [recPat () [Field () "toString" (varPat () "toString") , Field () "show" (varPat () "show")]] [] (letExpr () (varPat () "show") (varExpr () "@showInt") (varExpr () "toString"))
          ])

    Right lenShow = simplified foo3
    --foo3 = lamExpr () (varPat () "d") (lamExpr () (varPat () "x") (litExpr () (LInt 8))) -- (appExpr () [varExpr () "@length", appExpr () [varExpr () "show", varExpr () "d", varExpr () "x"]]))
    foo3 = lamExpr () (varPat () "d") (lamExpr () (varPat () "x") (appExpr () [varExpr () "@strlen", appExpr () [varExpr () "show", varExpr () "d", varExpr () "x"]]))


--runPipeline :: PatternExpr t -> Either String (PatternExpr NodeInfo, Environments)
runPipeline a = do
    x <- runExcept f
    case x of
        Nothing -> Left "error rererarre"
        Just x  -> Right x
            --case simplified (mapTags nodeType x) of
            --    Left e -> Left "..."
            --    Right r -> Right r
  where
--    f :: (MonadError String m) => m (Maybe (PatternExpr NodeInfo, Environments))
    f = runMaybeT (evalSupplyT (runReaderT (pipeline a) (myClassEnv, myTypeEnv)) (numSupply "a"))

--runTest2_ :: Either String (PatternExpr NodeInfo)
--runTest2_ = runPipeline expr22
--runTest2_ = runPipeline expr2
--runTest2_ = runPipeline expr35
--runTest2_ = runPipeline expr24
--runTest2_ = runPipeline expr25
--runTest2_ = runPipeline expr26
--runTest2_ = runPipeline expr29
--runTest2_ = runPipeline expr35
--runTest2_ = runPipeline expr3
--runTest2_ = runPipeline expr6
runTest2_ = runPipeline expr241

--
--


type1 :: TypeT a
type1 = tVar kTyp "a" `tArr` tVar kTyp "b"



main :: IO ()
main = putStrLn "hello world"

{-

Tau.Lang.Expr
Tau.Lang.Type
Tau.Lang.Parser


    |
   \ /
    |

Tau.Comp
Tau.Comp.TypeChecker
Tau.Comp.CodeGen


   -}


hello123 = 
    compile 
        [litExpr () (LInt 11), litExpr () (LInt 85)] 
        [ Clause [litPat () (LInt 1), litPat () (LInt 2)] [] (varExpr () "one") 
--        [ Clause [varPat () "zz1", varPat () "zz2"] [eqOp () (varExpr () "zz1") (litExpr () (LInt 1)), eqOp () (varExpr () "zz2") (litExpr () (LInt 2))] (varExpr () "one") 
        , Clause [varPat () "xxx", varPat () "yyy"] [] (varExpr () "two") 
        ]

hello1234 = pretty r
  where
    Right r = runSimplify hello123

