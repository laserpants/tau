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
import Tau.Lang.Pretty.Ast
import Tau.TestEnvs
import Tau.Util
import Test.Hspec
import Utils

type TestClause = Clause (Pattern () () ()) ProgExpr

succeedCompileAndEvalTo :: [TestClause] -> [Core] -> Value Eval -> SpecWith ()
succeedCompileAndEvalTo cs c val = do
    describe ("The pattern match clauses " <> prettyString cs <> " applied to " <> prettyString c) $
        it ("✔ compiles and evaluates to the value " <> prettyString val <> "\n") $
            --traceShow (evalExpr (cApp (foldr cLam core ls:c)) testValueEnv) $
                --(evalExpr (capp (foldr clam core ls:c)) testValueEnv == Just val)
                let xx = (evalExpr fooz testValueEnv)
                    in traceShow "&*****************************.>>>>>>>>>>>>>>>>>>" $ traceShow core $ traceShow c $ traceShow xx $ (xx  == Just val)
--                (evalExpr (cApp (foldr cLam core ls:c)) testValueEnv == Just val)
  where
    fooz = cApp ([core] <> c)
    Just core = do --evalSupply (toCore =<< compilePatterns (varExpr () <$> ls) =<< expandPatterns cs) (nameSupply "$")
        -- traceShow ((patExpr () (varExpr () <$> ls) cs)) $
        --     traceShow "/////////////////////////////" $
                --evalSupply (compileExpr (patExpr () (varExpr () <$> ls) cs)) (nameSupply "$")
                evalSupply (compileExpr (patExpr () [] cs)) (nameSupply "$")
--    ls = take (length c) letters

succeedCompileAndEvalTo1 :: ([TestClause], Core, Value Eval) -> SpecWith ()
succeedCompileAndEvalTo1 (cs, c, val) = succeedCompileAndEvalTo cs [c] val

succeedCompileAndEvalTo2 :: ([TestClause], Core, Core, Value Eval) -> SpecWith ()
succeedCompileAndEvalTo2 (cs, c, d, val) = succeedCompileAndEvalTo cs [c, d] val

testPatternCompiler :: SpecWith ()
testPatternCompiler = do

    pure ()

--    succeedCompileAndEvalTo1
--        ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [Guard [] (litExpr () (TBool True))]
--          , Clause [varPat () "a"] [Guard [] (litExpr () (TBool False))]
--          ] :: [TestClause]
--        , cApp [cVar "(::)", cLit (TInt 1), cApp [cVar "[]"]]
--        , Value (TBool True)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [Guard [] (litExpr () (TBool True))]
--          , Clause [varPat () "a"] [Guard [] (litExpr () (TBool False))]
--          ]
--        , cApp [cVar "[]"]
--        , Value (TBool False)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [litPat () (TBool True)] [Guard [] (litExpr () (TInt 1))]
--          , Clause [litPat () (TBool False)] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cLit (TBool False)
--        , Value (TInt 0)
--        )
--
--    succeedCompileAndEvalTo2
--        ( [ Clause [litPat () (TBool True), litPat () (TBool True)] [Guard [] (litExpr () (TInt 1))]
--          , Clause [litPat () (TBool False), litPat () (TBool False)] [Guard [] (litExpr () (TInt 0))]
--          , Clause [anyPat (), anyPat ()] [Guard [] (litExpr () (TInt (-1)))]
--          ]
--        , cLit (TBool True)
--        , cLit (TBool True)
--        , Value (TInt 1)
--        )
--
--    succeedCompileAndEvalTo2
--        ( [ Clause [litPat () (TBool True), litPat () (TBool True)] [Guard [] (litExpr () (TInt 1))]
--          , Clause [litPat () (TBool False), litPat () (TBool False)] [Guard [] (litExpr () (TInt 0))]
--          , Clause [anyPat (), anyPat ()] [Guard [] (litExpr () (TInt (-1)))]
--          ]
--        , cLit (TBool True)
--        , cLit (TBool False)
--        , Value (TInt (-1))
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [lstPat () [varPat () "x"]] [Guard [] (varExpr () "x")]
--          , Clause [lstPat () [varPat () "x", varPat () "y"]] [Guard [] (varExpr () "x")]
--          , Clause [lstPat () [varPat () "x", varPat () "y", varPat () "z"]] [Guard [] (varExpr () "x")]
--          , Clause [anyPat ()] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]
--        , Value (TInt 5)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [orPat () (lstPat () [varPat () "x"]) (orPat () (lstPat () [varPat () "x", anyPat ()]) (lstPat () [varPat () "x", anyPat (), anyPat ()]))] [Guard [] (varExpr () "x")]
--          , Clause [anyPat ()] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]
--        , Value (TInt 5)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [lstPat () [varPat () "x"]] [Guard [] (varExpr () "x")]
--          , Clause [lstPat () [varPat () "x", varPat () "y"]] [Guard [] (varExpr () "x")]
--          , Clause [lstPat () [varPat () "x", varPat () "y", varPat () "z"]] [Guard [] (varExpr () "x")]
--          , Clause [anyPat ()] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]]]
--        , Value (TInt 5)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [orPat () (lstPat () [varPat () "x"]) (orPat () (lstPat () [varPat () "x", anyPat ()]) (lstPat () [varPat () "x", anyPat (), anyPat ()]))] [Guard [] (varExpr () "x")]
--          , Clause [anyPat ()] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]]]
--        , Value (TInt 5)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [lstPat () [varPat () "x"]] [Guard [] (varExpr () "x")]
--          , Clause [lstPat () [varPat () "x", varPat () "y"]] [Guard [] (varExpr () "x")]
--          , Clause [lstPat () [varPat () "x", varPat () "y", varPat () "z"]] [Guard [] (varExpr () "x")]
--          , Clause [anyPat ()] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]]]]
--        , Value (TInt 0)
--        )
--
--    succeedCompileAndEvalTo1
--        ( [ Clause [orPat () (lstPat () [varPat () "x"]) (orPat () (lstPat () [varPat () "x", anyPat ()]) (lstPat () [varPat () "x", anyPat (), anyPat ()]))] [Guard [] (varExpr () "x")]
--          , Clause [anyPat ()] [Guard [] (litExpr () (TInt 0))]
--          ]
--        , cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]]]]
--        , Value (TInt 0)
--        )


--    --    | (x :: xs)
--    --      when x > 3 => 0
--    --      when x < 3 => 1
--    --      otherwise  => 2
--    --    | []         => 5
--    --      
--    succeedCompileAndEvalTo1
--        ( [ Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
--              [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
--              , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
--              , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
--              ]
--          , Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 5))] ] :: [TestClause]
--        --, cApp [cVar "(::)", cLit (TInt 3), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cApp [cVar "(::)", cLit (TInt 5), cVar "[]"]]]]
--        , cApp [cVar "(::)", cLit (TInt 3), cVar "[]"]
--        , Value (TInt 2)
--        )
