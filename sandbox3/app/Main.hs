{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Arrow (second, first)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Maybe (fromJust)
import Data.Void
import Tau.Comp.Patterns
import Tau.Env (Env)
import Tau.Eval
import Tau.Eval.Repl
import Tau.Expr
import Tau.Lang.Parser
import Tau.Pretty
import Tau.PrettyTree
import Tau.Prim
import Tau.Stuff
import Tau.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Tau.Env as Env


--data FlatList = FlatNil | FlatCons Int FlatList
--
--data RecList a = RecNil | RecCons Int a
--    deriving (Show, Functor, Foldable)
--
--_lengthAlg :: Algebra RecList Int
--_lengthAlg RecNil = 0
--_lengthAlg (RecCons _ n) = 1 + n
--
--_length :: Fix RecList -> Int
--_length = cata _lengthAlg
--
--_xs = Fix (RecCons 5 (Fix (RecCons 4 (Fix RecNil))))
--
--tail :: Fix RecList -> Maybe (Fix RecList)
--tail (Fix RecNil) = Nothing
--tail (Fix (RecCons _ xs)) = Just xs


--bork :: Int -> [a]
--bork = cata alg where
--    alg :: Algebra NatF [a]
--    alg = undefined


--

-- length : List a -> Nat
-- length = 
--   fun 
--     | [] => Zero
--     | (x :: xs) => Succ (length xs)

-- length : List a -> Nat
-- length = 
--   cata
--     | [] => Zero
--     | (x :: xs) => Succ xs


--
--

expr1 :: PatternExpr ()
expr1 = letExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")
expr2 = letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", litExpr () (LInt 5)])
expr3 = lam2Expr () [varPat () "x"] (appExpr () [varExpr () "lenShow", varExpr () "x"])
expr4 = lam2Expr () [varPat () "x"] (letExpr () (varPat () "f") (varExpr () "lenShow") (appExpr () [varExpr () "f", varExpr () "x"]))
expr5 = letExpr () (varPat () "f") (varExpr () "lenShow") (lam2Expr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))
expr6 = appExpr () [varExpr () "lenShow", litExpr () (LInt 555)]
expr7 = lam2Expr () [varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"])
expr8 = lam2Expr () [varPat () "x"] (lam2Expr () [varPat () "y"] (appExpr () [varExpr () "f", lam2Expr () [varPat () "x"] (lam2Expr () [varPat () "y"] (varExpr () "z"))]))
expr9 = lam2Expr () [varPat () "x"] (appExpr () [varExpr () "lenShow2", varExpr () "x"])
expr99 = appExpr () [lam2Expr () [varPat () "f"] (appExpr () [varExpr () "f", litExpr () (LInt 5)]), varExpr () "lenShow"]
expr20 = letExpr () (varPat () "id") (lam2Expr () [varPat () "x"] (varExpr () "x")) 
              (appExpr () [
                  varExpr () "(,)"
                , appExpr () [varExpr () "id", litExpr () (LInt 5)]
                , appExpr () [varExpr () "id", litExpr () (LBool True)]
              ])
expr21 = lam2Expr () [varPat () "x"] (letExpr () (varPat () "f") (lam2Expr () [varPat () "y"] (varExpr () "x")) (litExpr () (LInt 1)))
expr22 = lam2Expr () [varPat () "x"] (letExpr () (varPat () "f") (varExpr () "lenShow2") (appExpr () [varExpr () "f", varExpr () "x"]))
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

--expr25 = letExpr () (varPat () "show") (varExpr () "@showInt") (appExpr () [varExpr () "toString", litExpr () (LInt 5)])
expr25 = appExpr () [varExpr () "toString", litExpr () (LInt 5)]

expr26 = appExpr () [lam2Expr () [varPat () "x"] (appExpr () [varExpr () "toString", varExpr () "x"]), litExpr () (LInt 5)]

expr27 :: PatternExpr ()
expr27 = matExpr () [recExpr () [Field () "a" (litExpr () (LInt 5))]] [Clause [recPat () [Field () "a" (varPat () "b")]] [] (varExpr () "b")]

expr28 = letExpr () 
            (varPat () "f") 
            (lam2Expr () [varPat () "d"] (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "toString" (varPat () "toString")]] [] (varExpr () "toString")]))
            (appExpr () [varExpr () "f", recExpr () [Field () "toString" (varExpr () "@showInt")], litExpr () (LInt 5)])

expr29 = letExpr () 
            (varPat () "f") (lam2Expr () [varPat () "d"] (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "show" (varPat () "show"), Field () "toString" (varPat () "toString")]] [] (letExpr () (varPat () "show") (varExpr () "@showInt") (varExpr () "toString"))]))
            (appExpr () [varExpr () "f", recExpr () [Field () "show" (varExpr () "@showInt"), Field () "toString" (varExpr () "show")], litExpr () (LInt 5)])


expr30 = varExpr () "toString"

expr31 = letExpr () (varPat () "f") (lam2Expr () [recPat () [Field () "stuff" (varPat () "x")]] (varExpr () "x")) (appExpr () [varExpr () "f", recExpr () [Field () "stuff" (litExpr () (LInt 5))]])

expr32 = appExpr () [varExpr () "toString", litExpr () (LInt 5)]

expr33 = letExpr () (varPat () "toStringInt") (varExpr () "show") 
              (appExpr () 
                [ (lam2Expr () [varPat () "d"] (matExpr () [varExpr () "d"] [Clause [recPat () [Field () "toString" (varPat () "toString")]] [] (varExpr () "toString")]))
                , (recExpr () [Field () "toString" (varExpr () "toStringInt")])
                , (litExpr () (LInt 5))
              ])

expr34 = letExpr () (varPat () "f") (varExpr () "show") (appExpr () [varExpr () "f", litExpr () (LInt 5)])

expr35 = letExpr () (varPat () "f") (varExpr () "show") (appExpr () [lam2Expr () [varPat () "x"] (varExpr () "f"), litExpr () LUnit, litExpr () (LInt 5)])

expr36 = -- appExpr () [varExpr () "@strconcat", litExpr () (LString "List : "), 
    appExpr () [letExpr () (varPat () "showList") (lam2Expr () [varPat () "xs"] (appExpr () [varExpr () "@strconcat3", litExpr () (LString "List"), litExpr () (LString " ::: "), appExpr () [varExpr () "show", appExpr () [varExpr () "head", varExpr () "xs"]]])) (lam2Expr () [varPat () "x"] (appExpr () [varExpr () "show", appExpr () [varExpr () "singleton", varExpr () "x"]])), litExpr () (LInt 9)]


expr37 =
    letExpr () (varPat () "first") (lam2Expr () [varPat () "a"] (lam2Expr () [varPat () "b"] (varExpr () "a"))) (appExpr () [varExpr () "first", litExpr () (LInt 1), litExpr () (LInt 2)])

expr38 :: PatternExpr ()
expr38 =
    appExpr () [varExpr () "show", conExpr () "(,)" [litExpr () (LInt 9), litExpr () (LBool True)]]

expr991 = appExpr () [lam2Expr () [varPat () "f"] (appExpr () [varExpr () "f", litExpr () (LInt 5)]), varExpr () "lenShow"]


--    --                                 Int -> Bool -> String -> Unit
--    , ( "fn1"          , Forall [] [] (tInt `tArr` tBool `tArr` tString `tArr` tUnit) )
expr992 = lam2Expr () [varPat () "x", varPat () "y", varPat () "z"] (appExpr () [varExpr () "fn1", varExpr () "x", varExpr () "y", varExpr () "z"])

expr993 = fixExpr () "len" (lam2Expr () [varPat () "xs"] (matExpr () [varExpr () "xs"] [Clause [conPat () "Nil" []] [] (litExpr () (LInt 0)), Clause [conPat () "Cons" [anyPat (), varPat () "ys"]] [] (addOp () (litExpr () (LInt 1)) (appExpr () [varExpr () "len", varExpr () "ys"]))])) (appExpr () [varExpr () "len", conExpr () "Cons" [litExpr () (LInt 5), conExpr () "Cons" [litExpr () (LInt 4), conExpr () "Nil" []]]])

--expr993 = letExpr () (varPat () "len") 
--                  (lam2Expr () [varPat () "xs"] (matExpr () [varExpr () "xs"] [Clause [conPat () "Nil" []] [] (litExpr () (LInt 0)), Clause [conPat () "Cons" [anyPat (), varPat () "ys"]] [] (addOp () (litExpr () (LInt 1)) (appExpr () [varExpr () "len", varExpr () "ys"]))])) 
--                  (appExpr () [varExpr () "len", conExpr () "Cons" [litExpr () (LInt 5), conExpr () "Cons" [litExpr () (LInt 4), conExpr () "Nil" []]]])


{-

xxList :: (X a) => [a] -> String
xxList = undefined

class X a where
    xx :: a -> String

instance X [a] where
    xx = xxList

-}

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
    [ ( "@strlen"      , Forall [] [] (upgrade  (tString `tArr` tInt)) )
    , ( "@showInt"     , Forall [] [] (upgrade  (tInt `tArr` tString)) )
    , ( "@strconcat"   , Forall [] [] (upgrade tString `tArr` upgrade tString `tArr` upgrade tString) )
    , ( "@strconcat3"  , Forall [] [] (upgrade tString `tArr` upgrade tString `tArr` upgrade tString `tArr` upgrade tString) )
    , ( "lenShow"      , Forall [kTyp, kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tInt) ) 
    , ( "lenShow2"     , Forall [kTyp, kTyp] [InClass "Show" 0, InClass "Eq" 0] (tGen 0 `tArr` upgrade tInt) ) 
    , ( "(,)"          , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tGen 1 `tArr` (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 0)) (tGen 1))))
    , ( "Nil"          , Forall [kTyp] [] (tApp (upgrade tListCon) (tGen 0)) )
    , ( "Cons"         , Forall [kTyp] [] (tGen 0 `tArr` tApp (upgrade tListCon) (tGen 0) `tArr` tApp (upgrade tListCon) (tGen 0)) )
    , ( "(==)"         , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` upgrade tBool) )
    , ( "toString"     , Forall [kTyp] [InClass "ToString" 0] (tGen 0 `tArr` upgrade tString) )
    , ( "show"         , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` upgrade tString) )
    , ( "singleton"    , Forall [kTyp] [] (tGen 0 `tArr` (tApp (upgrade tListCon) (tGen 0))) )
    , ( "head"         , Forall [kTyp] [] (tApp (upgrade tListCon) (tGen 0) `tArr` tGen 0))
    , ( "fst"          , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` (tGen 0)))
    , ( "snd"          , Forall [kTyp, kTyp] [] (tPair (tGen 0) (tGen 1) `tArr` (tGen 1)))
    --                                 Int -> Bool -> String -> Unit
    , ( "fn1"          , Forall [] [] (tInt `tArr` tBool `tArr` tString `tArr` tUnit) )
    , ( "(+)"  , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    ]

--    [ -- ( "@strlen" , sScheme (tCon kStar "String" `tArr` tCon kStar "Int") )
--    , -- ( "show"    , sForall kStar ["Show"] (sScheme (tGen 0 `tArr` tCon kStar "String")) )

--type ClassEnv a = Env (Class a)
--type Class a = ([Name], [Instance a])

foo11 = varExpr (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "showList"

--foo11 = lamExpr undefined (varPat undefined "xs") (appExpr undefined [varExpr undefined "show", appExpr undefined [varExpr () "head", varExpr undefined "xs"]])

--showPair :: PatternExpr NodeInfo
--showPair = 
--    case runExcept (runMaybeT (evalSupplyT (runReaderT (comp zork) (myClassEnv, myTypeEnv)) (numSupply "a"))) of
--        Left e  -> error (show e)
--        Right x -> fromJust x
--  where
----    zork = lamExpr () (varPat () "p") (appExpr () [varExpr () "show", (appExpr () [varExpr () "fst", varExpr () "p"])])
--    zork = lamExpr () (varPat () "p") (appExpr () [varExpr () "show", (appExpr () [varExpr () "fst", varExpr () "p"])])
--    comp e = do
--        (tree, (sub, xxx1)) <- runStateT (infer e) mempty
--        let tree2 = (mapTags (apply sub) tree) 
--        pure tree2
--        --(tree4, _) <- withReaderT (\(a,b) -> (a,b,[])) (runStateT (rebuildTree22 tree2) [])
--        --let zzz3 = simplified (mapTags nodeType tree4)
--        --let Right zzz1 = zzz3
--        --pure zzz1


-- \p -> show (fst p)
showPair_ = lam2Expr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) [varPat (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"] 
              (appExpr (NodeInfo tString []) [varExpr (NodeInfo (tString `tArr` tString `tArr` tString `tArr` tString) []) "@strconcat3", appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "a" `tArr` tString) [InClass "Show" (tVar kTyp "a")]) "show", (appExpr (NodeInfo (tVar kTyp "a") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "a") []) "fst", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"])], litExpr (NodeInfo tString []) (LString ","), appExpr (NodeInfo tString []) [varExpr (NodeInfo (tVar kTyp "b" `tArr` tString) [InClass "Show" (tVar kTyp "b")]) "show", appExpr (NodeInfo (tVar kTyp "b") []) [varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tVar kTyp "b") []) "snd", varExpr (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b")) []) "p"]]])


myClassEnv :: ClassEnv (PatternExpr NodeInfo)
myClassEnv = Env.fromList
    [ ( "Show"
      , ( []
         , [ Instance [] tInt  (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tInt) [])  [Field (NodeInfo (tInt `tArr` tString) []) "show" (varExpr (NodeInfo (tInt `tArr` tString) []) "@showInt")])
           , Instance [] tBool (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [])  [Field (NodeInfo (tBool `tArr` tString) []) "show" (varExpr (NodeInfo (tBool `tArr` tString) []) "@showBool")])
           , Instance [InClass "Show" (tVar kTyp "a")] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tList (tVar kTyp "a"))) []) [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "show" foo11])
           , Instance [] (tPair (tVar kTyp "a") (tVar kTyp "b")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Show") (tPair (tVar kTyp "a") (tVar kTyp "b"))) []) [Field (NodeInfo (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "show" showPair_])
--           , Instance [] tBool (recExpr (tApp (tCon (kArr kTyp kTyp) "Show") tBool) [Field (tBool `tArr` tString) "show" (varExpr (tBool `tArr` tString) "@showBool")])
--           , Instance [] tUnit (recExpr (tApp (tCon (kArr kTyp kTyp) "Show") tUnit) [Field (tUnit `tArr` tString) "show" (varExpr (tUnit `tArr` tString) "@showUnit")])
--           0
           ]
        )
      )
    , ( "ToString"
      , ( [] -- ["Show"]
        -- , [ Instance [InClass "Show" tInt] tInt (recExpr (tApp (tCon (kArr kTyp kTyp) "ToString") tInt) [Field (tInt `tArr` tString) "toString" (varExpr (tInt `tArr` tString) "show")])
        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "ToString") tInt) []) [Field (NodeInfo (tInt `tArr` tString) []) "toString" (varExpr (NodeInfo (tInt `tArr` tString) [InClass "Show" tInt]) "show")])
          , Instance [] (tList (tVar kTyp "a")) (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "ToString") (tList (tVar kTyp "a"))) []) [Field (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) []) "toString" (varExpr (NodeInfo ((tList (tVar kTyp "a")) `tArr` tString) [InClass "Show" (tList (tVar kTyp "a"))]) "show")])
          ] )
      )
--    , ( "Eq"
--      , ( []
--        , [] )
--      )
    , ( "Num"
      , ( []
        , [ Instance [] tInt (recExpr (NodeInfo (tApp (tCon (kArr kTyp kTyp) "Num") tInt) []) [Field (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "(+)" (varExpr (NodeInfo (tInt `tArr` tInt `tArr` tInt) []) "@(+)Int")])
          ] 
        )
      )
    ]

--data X = X
--
--class Show a => Baz a where
--    baz :: a -> String
--
--instance Baz Int where
--    baz = show

--instance Baz X where
--    baz _ = ""

class ToString a where
    toString :: a -> String

instance Show a => ToString [a] where
   toString = show

-- class Show a => ToString a where
--     toString : a -> String

-- instance Show a => ToString a where
--    toString = show

-- instance ToString Int where
--    toString = show

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

    debugTree tree2
    traceShowM "==============================================================="

    let tree3 = tree2 -- (insertDicts xxx1 tree2)

    debugTree tree3
    
    --tree4 <- runReaderT (rebuildTree22 tree3) []
    (tree4, _) <- withReaderT (\(a,b) -> (a,b,[])) (runStateT (rebuildTree22 tree3) [])

    debugTree tree4

    --

    let zzz3 = simplified (mapTags nodeType tree4)
    --traceShowM zzz3
    let Right zzz1 = zzz3

    debugTree zzz1

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
--    debugTree zzz1
--    traceShowM "---"
--
--    let Just foo = evalExpr zzz1 myEvalEnv
--
--    traceShowM foo
--    traceShowM "==="
--
--    pure zzz1

myEvalEnv = Env.fromList 
    [ ("toString"   , fromJust (runEval (eval toString) mempty))
    , ("show"       , fromJust (runEval (eval show_) mempty))
    , ("lenShow"    , fromJust (runEval (eval lenShow) mempty))
    , ("(,)"        , Tau.Eval.constructor "(,)" 2) -- fromJust (runEval (eval pair) mempty))
    , ("Nil"        , Tau.Eval.constructor "Nil" 0) -- fromJust (runEval (eval pair) mempty))
    , ("Cons"       , Tau.Eval.constructor "Cons" 2) -- fromJust (runEval (eval pair) mempty))
    , ("singleton"  , fromJust (runEval (eval singleton ) mempty))
    , ("head"       , fromJust (runEval (eval head_) mempty))
    , ("fst"        , fromJust (runEval (eval fst_) mempty))
    , ("snd"        , fromJust (runEval (eval snd_) mempty))
    , ("(+)"        , fromJust (runEval (eval plus_) mempty))
    ]
  where
    Right plus_ = simplified foo123
    foo123 = lam2Expr () [varPat () "d"] (matExpr () [varExpr () "d"] [ Clause [recPat () [Field () "(+)" (varPat () "(+)")]] [] (varExpr () "(+)") ])

    Right snd_ = simplified foo25
    foo25 = lam2Expr () [varPat () "p"] (matExpr () [varExpr () "p"] [Clause [conPat () "(,)" [anyPat (), varPat () "b"]] [] (varExpr () "b")])

    Right fst_ = simplified foo24
    foo24 = lam2Expr () [varPat () "p"] (matExpr () [varExpr () "p"] [Clause [conPat () "(,)" [varPat () "a", anyPat ()]] [] (varExpr () "a")])

    Right head_ = simplified foo23
    foo23 = lam2Expr () [varPat () "xs"] (matExpr () [varExpr () "xs"] [Clause [conPat () "Cons" [varPat () "x", anyPat ()]] [] (varExpr () "x")])

    Right singleton = simplified foo22
    foo22 = lam2Expr () [varPat () "x"] (conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []])

    Right show_ = simplified foo2
    foo2 = lam2Expr () [varPat () "d"] (matExpr () [varExpr () "d"] [ Clause [recPat () [Field () "show" (varPat () "show")]] [] (varExpr () "show") ])

    Right toString = simplified foo
--  -- \d => match d with | { toString = toString } => toString 
    foo = lam2Expr () [varPat () "d"] (matExpr () [varExpr () "d"] 
          [ Clause [recPat () [Field () "toString" (varPat () "toString") ]] [] ((varExpr () "toString"))
          ])

    Right lenShow = simplified foo3
    --foo3 = lamExpr () (varPat () "d") (lamExpr () (varPat () "x") (litExpr () (LInt 8))) -- (appExpr () [varExpr () "@length", appExpr () [varExpr () "show", varExpr () "d", varExpr () "x"]]))
    foo3 = lam2Expr () [varPat () "d"] (lam2Expr () [varPat () "x"] (appExpr () [varExpr () "@strlen", appExpr () [varExpr () "show", varExpr () "d", varExpr () "x"]]))


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
--runTest2_ = runPipeline expr32
--runTest2_ = runPipeline expr35
--runTest2_ = runPipeline expr3
--runTest2_ = runPipeline expr6
--runTest2_ = runPipeline expr25
--runTest2_ = runPipeline $ appExpr () [expr5, litExpr () (LInt 55555)]
--runTest2_ = runPipeline expr38
runTest2_ = runPipeline expr993

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

