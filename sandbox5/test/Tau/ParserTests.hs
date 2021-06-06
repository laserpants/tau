{-# LANGUAGE OverloadedStrings #-}
module Tau.ParserTests where

import Data.Either (isLeft)
import Tau.Lang
import Tau.Parser
import Tau.Tool
import Tau.Type
import Test.Hspec hiding (describe, it)
import Text.Megaparsec
import Utils

suceedParse :: (Eq a) => Parser a -> Text -> a -> SpecWith ()
suceedParse parser input expected =
    describe input $
        it "✔ parses to ...TODO..." $
            result == expected
  where
    Right result = runParser parser "" input

failParse :: (Eq a) => Parser a -> Text -> SpecWith ()
failParse parser input =
    describe input $
        it "✗ fails to parse" $
            isLeft (runParser parser "" input)

testPatternParser :: SpecWith ()
testPatternParser = do

    suceedParse patternParser
        "x"
        (varPat () "x")

    suceedParse patternParser
        "5"
        (litPat () (TInteger 5))

    suceedParse patternParser
        "Some(x)"
        (conPat () "Some" [varPat () "x"])

    suceedParse patternParser
        "None"
        (conPat () "None" [])

    suceedParse patternParser
        "_"
        (anyPat ())

    suceedParse patternParser
        "(4, 3)"
        (tuplePat () [litPat () (TInteger 4), litPat () (TInteger 3)])

    suceedParse patternParser
        "x or 5"
        (orPat () (varPat () "x") (litPat () (TInteger 5)))

    suceedParse patternParser
        "{ x = 5 }"
        (recordPat () (rowPat () "x" (litPat () (TInteger 5)) Nothing))

    suceedParse patternParser
        "{ x = 5 } as y"
        (asPat () "y" (recordPat () (rowPat () "x" (litPat () (TInteger 5)) Nothing)))

testAnnPatternParser :: SpecWith ()
testAnnPatternParser = do

    suceedParse annPatternParser
        "x : Int"
        (annPat tInt (varPat () "x"))

    suceedParse annPatternParser
        "5 : Int"
        (annPat tInt (litPat () (TInteger 5)))

    suceedParse annPatternParser
        "_ : Int"
        (annPat tInt (anyPat ()))

    suceedParse annPatternParser
        "(4, 3) : Int"
        (annPat tInt (tuplePat () [litPat () (TInteger 4), litPat () (TInteger 3)]))

    suceedParse annPatternParser
        "(x or 5) : Int"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    suceedParse annPatternParser
        "x or 5 : Int"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    suceedParse annPatternParser
        "(x or 5 : Int)"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    suceedParse annPatternParser
        "((x or 5 : Int))"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    suceedParse annExprParser
        "let f(x : Int) = x in f"
        (letExpr () (BFun () "f" [annPat tInt (varPat () "x")]) (varExpr () "x") (varExpr () "f"))

    suceedParse annPatternParser
        "_ as x : Int"
        (annPat tInt (asPat () "x" (anyPat ())))

    suceedParse annPatternParser
        "((_ as x : Int))"
        (annPat tInt (asPat () "x" (anyPat ())))

testExprParser :: SpecWith ()
testExprParser = do

    suceedParse exprParser
        "x"
        (varExpr () "x")

    suceedParse exprParser
        "Some(x)"
        (conExpr () "Some" [varExpr () "x"])

    suceedParse exprParser
        "None"
        (conExpr () "None" [])

    suceedParse exprParser
        "(4, 3)"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    suceedParse exprParser
        "((4, 3))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    suceedParse exprParser
        "(((4, 3)))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    suceedParse exprParser
        "((((4, 3))))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    suceedParse exprParser
        "(1, 3, 4)"
        (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    suceedParse exprParser
        "if (4, 3) then (1, 3, 4) else (5, 6, 7)"
        (ifExpr () 
            (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]) 
            (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)]) 
            (tupleExpr () [litExpr () (TInteger 5), litExpr () (TInteger 6), litExpr () (TInteger 7)]))

    suceedParse exprParser
        "fn(1, 3, 4)"
        (appExpr () [varExpr () "fn", litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    suceedParse exprParser
        "fn (1, 3, 4)"
        (appExpr () [varExpr () "fn", litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    suceedParse exprParser
        "fn(x, 3, 4)"
        (appExpr () [varExpr () "fn", varExpr () "x", litExpr () (TInteger 3), litExpr () (TInteger 4)])

    suceedParse exprParser
        "(fn(x))(y)"
        (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

    suceedParse exprParser
        "[1,2,3]"
        (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3)])

    suceedParse exprParser
        "let x = (1, 2) in z"
        (letExpr () (BLet () (varPat () "x")) (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)]) (varExpr () "z"))

    suceedParse exprParser
        "let f(x) = (1, 2) in z"
        (letExpr () (BFun () "f" [varPat () "x"]) (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)]) (varExpr () "z"))

    suceedParse exprParser
        "{ x = 5 }"
        (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) Nothing))

    suceedParse exprParser
        "{ x = { y = 5 } }"
        (recordExpr () (rowExpr () "x" (recordExpr () (rowExpr () "y" (litExpr () (TInteger 5)) Nothing)) Nothing))

    suceedParse exprParser
        "(x) => x"
        (lamExpr () [varPat () "x"] (varExpr () "x"))

    suceedParse exprParser
        "(x) => { x = 5 }"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) Nothing)))

    suceedParse exprParser
        "((x) => { x = 5 })"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) Nothing)))

    suceedParse exprParser
        "((x) => ({ x = 5 }))"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) Nothing)))

    suceedParse exprParser
        "(x) => x + 1"
        (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))

    suceedParse exprParser
        "((x) => x + 1)(5)"
        (appExpr () 
            [ lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
            , litExpr () (TInteger 5) ])

    suceedParse exprParser
        "let f = (x) => x + 1 in y"
        (letExpr () (BLet () (varPat () "f")) 
            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))
            (varExpr () "y"))

    suceedParse exprParser
        "let withDefault | Some(y) => y | None => 0 in Some(3)"
        (letExpr () (BLet () (varPat () "withDefault")) 
            (funExpr ()
                [ Clause () (conPat () "Some" [varPat () "y"]) [Guard [] (varExpr () "y")]
                , Clause () (conPat () "None" []) [Guard [] (litExpr () (TInteger 0))] 
                ])
            (conExpr () "Some" [litExpr () (TInteger 3)]))

    suceedParse exprParser
        "let withDefault(val) | Some(y) => y | None => val in Some(3)"
        (letExpr () (BFun () "withDefault" [varPat () "val"]) 
            (funExpr ()
                [ Clause () (conPat () "Some" [varPat () "y"]) [Guard [] (varExpr () "y")]
                , Clause () (conPat () "None" []) [Guard [] (varExpr () "val")] 
                ])
            (conExpr () "Some" [litExpr () (TInteger 3)]))

testExprParserMatch :: SpecWith ()
testExprParserMatch = do

    suceedParse exprParser
        "match x with | 4 => { a = 5 }"
        (patExpr () (varExpr () "x") 
            [ Clause () (litPat () (TInteger 4)) 
                  [ Guard [] (recordExpr () (rowExpr () "a" (litExpr () (TInteger 5)) Nothing)) ]
            ])

    suceedParse exprParser
        "match x with | 4 => { a = 5 } | 5 => { a = 7 }"
        (patExpr () (varExpr () "x") 
            [ Clause () (litPat () (TInteger 4)) 
                  [ Guard [] (recordExpr () (rowExpr () "a" (litExpr () (TInteger 5)) Nothing)) ]
            , Clause () (litPat () (TInteger 5)) 
                  [ Guard [] (recordExpr () (rowExpr () "a" (litExpr () (TInteger 7)) Nothing)) ]
            ])

    suceedParse exprParser
        "match x with | y iff y > 5 => True"
        (patExpr () (varExpr () "x") 
            [ Clause () (varPat () "y") 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5))] (litExpr () (TBool True)) ]
            ])

    suceedParse exprParser
        "match x with | y iff y > 5 => 0 iff y > 1 => 1 otherwise => 2"
        (patExpr () (varExpr () "x") 
            [ Clause () (varPat () "y") 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5))] (litExpr () (TInteger 0)) 
                  , Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) 
                  , Guard [] (litExpr () (TInteger 2)) 
                  ]
            ])

    suceedParse exprParser
        "x.f"
        (appExpr () [varExpr () "f", varExpr () "x"])

    suceedParse exprParser
        "xs.map(f)"
        (appExpr () [appExpr () [varExpr () "map", varExpr () "f"], varExpr () "xs"]) 

    suceedParse exprParser
        "xs.map((x) => x + 1)"
        (appExpr () [appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))], varExpr () "xs"]) 

testAnnExprParser :: SpecWith ()
testAnnExprParser = do

    failParse annExprParser "!5"

    suceedParse annExprParser
        "4"
        (litExpr () (TInteger 4))

    suceedParse annExprParser
        "4 : Int"
        (annExpr tInt (litExpr () (TInteger 4)))

    suceedParse annExprParser
        "(4 : Int)"
        (annExpr tInt (litExpr () (TInteger 4)))

    suceedParse annExprParser
        "(4)"
        (litExpr () (TInteger 4))

    suceedParse annExprParser
        "((4))"
        (litExpr () (TInteger 4))

    suceedParse annExprParser
        "((4) : Int)"
        (annExpr tInt (litExpr () (TInteger 4)))

    suceedParse annExprParser
        "(4) : Int"
        (annExpr tInt (litExpr () (TInteger 4)))

    suceedParse annExprParser
        "((4, 3) : Int)"
        (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))

    suceedParse annExprParser
        "(((4, 3)))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    suceedParse annExprParser
        "((((4, 3))))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    failParse annExprParser
        "((((4, 3)]]]"

    suceedParse annExprParser
        "(((4, 3) : Int))"
        (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))

    suceedParse annExprParser
        "(4, 3) : Int"
        (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))

    suceedParse annExprParser
        "if (4, 3) : Int then (1, 3, 4) else (5, 6, 7)"
        (ifExpr () 
            (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))
            (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)]) 
            (tupleExpr () [litExpr () (TInteger 5), litExpr () (TInteger 6), litExpr () (TInteger 7)]))

    suceedParse annExprParser
        "(if (4, 3) : Int then (1, 3, 4) else (5, 6, 7)) : Int"
        (annExpr tInt (ifExpr () 
            (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))
            (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)]) 
            (tupleExpr () [litExpr () (TInteger 5), litExpr () (TInteger 6), litExpr () (TInteger 7)])))

    suceedParse annExprParser
        "fn(1 : Int, 3, 4)"
        (appExpr () [varExpr () "fn", annExpr tInt (litExpr () (TInteger 1)), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    suceedParse annExprParser
        "fn(1 : Int, 3, 4) : Int"
        (annExpr tInt (appExpr () [varExpr () "fn", annExpr tInt (litExpr () (TInteger 1)), litExpr () (TInteger 3), litExpr () (TInteger 4)]))

    suceedParse annExprParser
        "fn(x : Int, 3, 4)"
        (appExpr () [varExpr () "fn", annExpr tInt (varExpr () "x"), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    suceedParse annExprParser
        "((fn(x))(y))"
        (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

    suceedParse exprParser
        "[1 : Int, 2, 3]"
        (listExpr () [annExpr tInt (litExpr () (TInteger 1)), litExpr () (TInteger 2), litExpr () (TInteger 3)])

    suceedParse exprParser
        "let x = (1, 2) : Int in z"
        (letExpr () (BLet () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])) (varExpr () "z"))

    suceedParse exprParser
        "let x = (1, 2) : Int in z : Int"
        (letExpr () (BLet () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])) (annExpr tInt (varExpr () "z")))

    suceedParse annExprParser
        "(let x = (1, 2) : Int in z : Int) : Int"
        (annExpr tInt (letExpr () (BLet () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])) (annExpr tInt (varExpr () "z"))))

    suceedParse annExprParser
        "{ x = 5 : Int }"
        (recordExpr () (rowExpr () "x" (annExpr tInt (litExpr () (TInteger 5))) Nothing))
