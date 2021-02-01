{-# LANGUAGE OverloadedStrings     #-}
module Main where

import Tau.Eval
import Tau.Expr
import Tau.Expr.Main
import Tau.Pretty
import Tau.PrettyTree
import Tau.Prim
import Tau.Stuff
import Tau.Type
import Tau.Type.Main
import qualified Tau.Env as Env


--
--

runTest1_ = do
    let Right (tree, sub) = runTest1 
    debugTree tree
    debugTree (mapTags (apply sub) tree)

runTest1 = runInfer mempty typeEnv (infer expr1) where
  typeEnv = Env.fromList [ ("lenShow", forall kTyp "a" ["Show"] (scheme (tGen 0 `tArr` upgrade tInt))) ]

--
--

expr1 :: PatternExpr ()
expr1 = letExpr () (varPat () "f") (varExpr () "lenShow") (varExpr () "f")

type1 :: Type a
type1 = tVar kTyp "a" `tArr` tVar kTyp "b"



main :: IO ()
main = putStrLn "hello world"
