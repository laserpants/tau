{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main where

import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.List
import Tau.Expr
import Tau.Expr.Patterns
import Tau.Type
import Tau.Type.Solver
import Tau.Type.Substitution
import Tau.Type.Inference
import Data.Function ((&))
import Tau.Eval
import Tau.Util
import qualified Tau.Env as Env
import Tau.Env
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

testEnv :: ConstructorEnv
testEnv = constructorEnv 
    [ ("Cons" , ["Cons", "Nil"]) 
    , ("Nil"  , ["Cons", "Nil"]) 
    ]

abcdef1 =
    letExpr () 
        (conPat () "Just" [varPat () "x"]) 
        (conExpr () "Just" [litExpr () (LInt 5)])
        (varExpr () "x")

abcdef2 = infer abcdef1

abcdef3 = r
  where
    Right (r, _, _) = runInfer abcdef2

abcdef4 = simplify abcdef3

abcdef5 = r
  where
    Right r = runSimplify abcdef4

abcdef6 = evalExpr abcdef5 $ Env.fromList 
    [ ("Just", constructor "Just" 1)
    ]





--ccc1 :: [[Pattern t]]
ccc1 =
    [ [ conPat () "Cons" [ litPat () (LInt 5), conPat () "Nil" []                                 ] ]
    , [ conPat () "Cons" [ litPat () (LInt 4), conPat () "Cons" [ varPat () "y", varPat () "ys" ] ] ]
    , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
    , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
    , [ conPat () "Nil"  []                                                                         ]                                                  
    , [ varPat () "xs"                                                                              ]
    ]

ddd1 :: Bool
ddd1 = runReader (exhaustive ccc1) testEnv 


--ccc2 :: [[Pattern]]
ccc2 =
    [ [ conPat () "Cons" [ litPat () (LInt 5), conPat () "Nil" []                                 ] ]
    , [ conPat () "Cons" [ litPat () (LInt 4), conPat () "Cons" [ varPat () "y", varPat () "ys" ] ] ]
    , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
    , [ conPat () "Cons" [ varPat () "x", conPat () "Cons" [ varPat () "y", conPat () "Nil" []  ] ] ]
    , [ conPat () "Nil"  []                                                                         ]
    ]

ddd2 :: Bool
ddd2 = runReader (exhaustive ccc2) testEnv 


--ccc3 :: [[Pattern]]
ccc3 =
    [ [ conPat () "Nil" [], conPat () "Nil" [] ] 
    ]

ddd3 :: Bool
ddd3 = runReader (exhaustive ccc3) testEnv 


--ccc4 :: [[Pattern]]
ccc4 =
    [ [ conPat () "Nil" [], conPat () "Nil" [] ] 
    , [ conPat () "Nil" [], conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
    ]

ddd4 :: Bool
ddd4 = runReader (exhaustive ccc4) testEnv 

--ccc5 :: [[Pattern]]
ccc5 =
    [ [ conPat () "Nil" []                                 , conPat () "Nil" [] ] 
    , [ conPat () "Nil" []                                 , conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
    , [ conPat () "Cons" [ varPat () "x", varPat () "xs" ] , conPat () "Nil" [] ] 
    ]

ddd5 :: Bool
ddd5 = runReader (exhaustive ccc5) testEnv 


--ccc6 :: [[Pattern]]
ccc6 =
    [ [ conPat () "Nil" []                                 , conPat () "Nil" [] ] 
    , [ conPat () "Nil" []                                 , conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
    , [ conPat () "Cons" [ varPat () "x", varPat () "xs" ] , conPat () "Nil" [] ] 
    , [ conPat () "Cons" [ varPat () "x", varPat () "xs" ] , conPat () "Cons" [ varPat () "x", varPat () "xs" ] ] 
    ]

ddd6 :: Bool
ddd6 = runReader (exhaustive ccc6) testEnv 


--ccc7 :: [[Pattern]]
ccc7 =
    [ [ litPat () (LBool True) ] 
    , [ litPat () (LBool False) ]
    ]

ddd7 :: Bool
ddd7 = runReader (exhaustive ccc7) testEnv 


--ccc8 :: [[Pattern]]
ccc8 =
    [ [ litPat () (LBool True) ] 
    ]

ddd8 :: Bool
ddd8 = runReader (exhaustive ccc8) testEnv 





--data ThingF a = Case a
--
--type Thing = Fix ThingF
--
--
--yy1 = unfoldr fun 1
--  where
--    fun x = if x == 5 then Nothing else Just (x, x+1)

--data Thing = Case Thing | Base deriving (Show, Eq)
--
--yy1 = unfoldr fun 0
--  where
--    fun x = 
--        if x == 5 then Nothing
--                  else Just (Base, x + 1)

--data ThingF a = Case a | Base deriving (Show, Eq, Functor)
--
--deriveShow1 ''ThingF
--deriveEq1   ''ThingF
--
--type Thing = Fix ThingF
--
----yyy :: Int -> Thing
----yyy = ana coalg 
----  where
----    coalg 0 = Base
----    coalg n = Case (n - 1)
--
--
--
--xx1 :: Maybe [(Name, Value Eval)]
--xx1 = 
--    tryEquation 
--        [ PVar () "x", PVar () "y" ] 
--        [ Value (LInt 5), Value (LInt 3) ]
--
--xx2 :: Maybe [(Name, Value Eval)]
--xx2 = 
--    tryEquation 
--        [ PCon () "Just" [ "x" ] ] 
--        [ Data "Just" [ Value (LInt 2) ] ]
--
--xx3 :: Maybe [(Name, Value Eval)]
--xx3 = 
--    tryEquation 
--        [ PCon () "Just" [ "x" ] ] 
--        [ Data "Must" [ Value (LInt 2) ] ]
--
--newtype X a = X { unX :: SupplyT Name Maybe a } deriving
--    ( Functor
--    , Applicative
--    , Monad
--    , MonadSupply Name )
--
--instance MonadFail X where
--    fail _ = X (lift Nothing)
--
--xx5 :: X (Expr () (SimpleRep ()) Name)
--xx5 = simplify (matExpr () 
--    [varExpr () "xs"] 
--    [Equation [Fix (PCon () "Cons" [Fix (PVar () "x"), Fix (PCon () "Cons" [Fix (PVar () "y"), Fix (PVar () "ys")])])] [] (varExpr () "e1")]
--    )
--
--runX :: X b -> Maybe b
--runX x = evalSupplyT (unX x) []
--
--xx6 = runX xx5
--
----
--
--xx7 = conGroups 
--    [ Equation [Fix (PCon () "Cons" [Fix (PVar () "x"), Fix (PLit () (LInt 5))])] [] (varExpr () "e1") 
--    , Equation [Fix (PCon () "Cons" [Fix (PVar () "x"), Fix (PVar () "xs")])] [] (varExpr () "e2") 
--    , Equation [Fix (PCon () "Nil" [])] [] (varExpr () "e3") 
--    ]
--
--
--xx8 :: PatternExpr ()
--xx8 =
--    ifExpr () 
--        (eqOp () (varExpr () "x") (varExpr () "y")) 
--        (litExpr () (LInt 5))
--        (litExpr () (LInt 3))
--
--xx9 :: Either InferError (PatternExpr Type, [TypeAssumption], [Constraint])
--xx9 =
--    runInfer (infer xx8)
--
----
--
---- let x = 3 in f x
--
----testExpr1 :: PatternExpr ()
----testExpr1 =
----    eLet 
----        (rVar () "x") 
----        (tagLit () (LInt 3)) 
----        (tagApp () [eVar "f", tagVar () "x"])
----
----test1 = r where Right r = runInfer (infer testExpr1)
----
------ let (Just x) = (Just 3) in x
----
----testRep2 :: Rep ()
----testRep2 = rCon () "Just" [rVar () "x"]
----
----testExpr2 :: PatternExpr ()
----testExpr2 =
----    eLet 
----        testRep2
----        (tagApp () [tagVar () "Just", tagLit () (LInt 3)]) 
----        (tagVar () "x")
----
----runTestRep2 :: (Rep Type, [TypeAssumption])
----runTestRep2 = r where Right r = runInfer (inferRep testRep2)
----
----test2 :: (RepExpr Type, [TypeAssumption], [Constraint])
----test2 = r where Right r = runInfer (infer testExpr2)
----
----test2Sub = sub
----  where
----    (tr, as, cs) = test2
----    Right (sub, tycls) = runInfer (solve cs)
----
----test22 :: Infer (RepExpr Type)
----test22 = do
----    (tr, as, cs) <- infer testExpr2
----    (sub, tycls) <- solve cs
----    pure (apply sub tr)
----
----runTest22 = runInfer test22
----
------
----
------ match x with 
------   | Just 3 :: [] => e1
------   | Just x :: [] => e2
------
----testExpr3 =
----    tagMatch ()
----      [tagVar () "x"]
----      [ Equation [pCon () "Cons" [pCon () "Just" [pLit () (LInt 3)], pCon () "Nil" []]] [] (tagVar () "e1") 
----      , Equation [pCon () "Cons" [pCon () "Just" [pVar () "x"], pCon () "Nil" []]] [] (tagVar () "e2") 
----      ]
----
----test3 = do
----    (tr, as, cs) <- infer testExpr3
----    pure tr
----
----runTest3 = runInfer test3


main :: IO ()
main = pure ()
