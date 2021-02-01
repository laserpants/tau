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
expr6 = appExpr () [varExpr () "lenShow", litExpr () (LInt 5)]
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


runTest1_ = do
    let Right (tree, (sub, _)) = runTest1 
    debugTree tree
    debugTree (mapTags (apply sub) tree)

runTest1 = runInfer mempty typeEnv (infer expr20) where
  typeEnv = Env.fromList 
        [ ("lenShow" , forall kTyp "a" ["Show"] (scheme (tGen 0 `tArr` upgrade tInt))) 
        , ("(,)"     , forall kTyp "a" [] (forall kTyp "b" [] (scheme (tGen 1 `tArr` tGen 0 `tArr` tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tGen 1)) (tGen 0)))))
        ]

--
--


type1 :: Type a
type1 = tVar kTyp "a" `tArr` tVar kTyp "b"



main :: IO ()
main = putStrLn "hello world"
