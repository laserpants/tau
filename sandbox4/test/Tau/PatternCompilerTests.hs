{-# LANGUAGE OverloadedStrings #-}
module Tau.PatternCompilerTests where

import Test.Hspec
import Utils

---- (fun | _ :: _ => True | _ => False) []
--testExpr29 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
--testExpr29 = appExpr () [patExpr () [] [Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True)), Clause [anyPat ()] [] (litExpr () (LBool False))], conExpr () "[]" []]
--
--testExpr30 :: Expr () (Pattern ()) (Binding (Pattern ())) [Pattern ()] (Op1 ()) (Op2 ())
--testExpr30 = patExpr () [] [Clause [conPat () "(::)" [anyPat (), anyPat ()]] [] (litExpr () (LBool True)), Clause [varPat () "x"] [] (litExpr () (LBool False))]

testPatternCompiler :: SpecWith ()
testPatternCompiler =
    pure ()
