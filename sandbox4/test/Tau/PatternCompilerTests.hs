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

type TestExpr = Expr () (Prep ()) Name Name Void Void NoListSugar NoFunPats
type TestClause = Clause (Pattern () () PatternsDesugared) TestExpr

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
        ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True))
          , Clause [varPat () "a"] [] (litExpr () (TBool False))
          ]
        , cApp [cVar "(::)", cLit (TInt 1), cApp [cVar "[]"]]
        , Value (TBool True)
        )

    succeedCompileAndEvalTo1
        ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (TBool True))
          , Clause [varPat () "a"] [] (litExpr () (TBool False))
          ]
        , cApp [cVar "[]"]
        , Value (TBool False)
        )

    succeedCompileAndEvalTo1
        ( [ Clause [litPat () (TBool True)] [] (litExpr () (TInt 1))
          , Clause [litPat () (TBool False)] [] (litExpr () (TInt 0))
          ]
        , cLit (TBool False)
        , Value (TInt 0)
        )

    succeedCompileAndEvalTo2
        ( [ Clause [litPat () (TBool True), litPat () (TBool True)] [] (litExpr () (TInt 1))
          , Clause [litPat () (TBool False), litPat () (TBool False)] [] (litExpr () (TInt 0))
          , Clause [anyPat (), anyPat ()] [] (litExpr () (TInt (-1)))
          ]
        , cLit (TBool True)
        , cLit (TBool True)
        , Value (TInt 1)
        )

    succeedCompileAndEvalTo2
        ( [ Clause [litPat () (TBool True), litPat () (TBool True)] [] (litExpr () (TInt 1))
          , Clause [litPat () (TBool False), litPat () (TBool False)] [] (litExpr () (TInt 0))
          , Clause [anyPat (), anyPat ()] [] (litExpr () (TInt (-1)))
          ]
        , cLit (TBool True)
        , cLit (TBool False)
        , Value (TInt (-1))
        )
