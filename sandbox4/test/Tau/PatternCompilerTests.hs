{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.PatternCompilerTests where

import Control.Monad.Supply 
import Data.Void
import Tau.Comp.Core
import Tau.Eval.Core
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Prog
import Tau.TestEnvs
import Tau.Util
import Test.Hspec
import Utils

type TestExpr   = Expr () (Prep ()) Name Name Void Void
type TestClause = Clause (Pattern () ()) TestExpr

succeedCompileAndEvalTo :: [TestClause] -> [Core] -> Value Eval -> SpecWith ()
succeedCompileAndEvalTo cs c val = do
    describe ("The pattern match clauses " <> prettyString cs <> " applied to " <> prettyString c) $
        it ("✔ compiles and evaluates to the value " <> prettyString val <> "\n")
            (evalExpr (cApp (foldr cLam core ls:c)) testValueEnv == Just val)
  where
    Just core = evalSupply (toCore =<< compilePatterns (varExpr () <$> ls) =<< expandPatterns cs) (nameSupply "$")
    ls = take (length c) letters

succeedCompileAndEvalTo1 :: ([TestClause], Core, Value Eval) -> SpecWith ()
succeedCompileAndEvalTo1 (cs, c, val) = succeedCompileAndEvalTo cs [c] val

succeedCompileAndEvalTo2 :: ([TestClause], Core, Core, Value Eval) -> SpecWith ()
succeedCompileAndEvalTo2 (cs, c, d, val) = succeedCompileAndEvalTo cs [c, d] val

testPatternCompiler :: SpecWith ()
testPatternCompiler = do

    succeedCompileAndEvalTo1
        ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True))
          , Clause [varPat () "a"] [] (litExpr () (LBool False))
          ]
        , cApp [cVar "(::)", cLit (LInt 1), cApp [cVar "[]"]]
        , Value (LBool True)
        )

    succeedCompileAndEvalTo1
        ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True))
          , Clause [varPat () "a"] [] (litExpr () (LBool False))
          ]
        , cApp [cVar "[]"]
        , Value (LBool False)
        )

    succeedCompileAndEvalTo1
        ( [ Clause [litPat () (LBool True)] [] (litExpr () (LInt 1))
          , Clause [litPat () (LBool False)] [] (litExpr () (LInt 0))
          ]
        , cLit (LBool False)
        , Value (LInt 0)
        )

    succeedCompileAndEvalTo2
        ( [ Clause [litPat () (LBool True), litPat () (LBool True)] [] (litExpr () (LInt 1))
          , Clause [litPat () (LBool False), litPat () (LBool False)] [] (litExpr () (LInt 0))
          , Clause [anyPat (), anyPat ()] [] (litExpr () (LInt (-1)))
          ]
        , cLit (LBool True)
        , cLit (LBool True)
        , Value (LInt 1)
        )

    succeedCompileAndEvalTo2
        ( [ Clause [litPat () (LBool True), litPat () (LBool True)] [] (litExpr () (LInt 1))
          , Clause [litPat () (LBool False), litPat () (LBool False)] [] (litExpr () (LInt 0))
          , Clause [anyPat (), anyPat ()] [] (litExpr () (LInt (-1)))
          ]
        , cLit (LBool True)
        , cLit (LBool False)
        , Value (LInt (-1))
        )
