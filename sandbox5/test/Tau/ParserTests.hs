{-# LANGUAGE OverloadedStrings #-}
module Tau.ParserTests where

import Data.Either (isLeft, isRight)
import Tau.Compiler.Unify
import Tau.Lang
import Tau.Parser
import Tau.Pretty
import Tau.Prog
import Tau.Tooling
import Tau.Type
import Test.Hspec hiding (describe, it)
import Text.Megaparsec
import Utils

succeedParseType :: Parser Type -> Text -> Type -> SpecWith ()
succeedParseType parser input expected =
    describe input $
        it ("✔ parses to " <> prettyPrint expected) $
            isRight $ do 
                result <- runParserStack parser "" input
                pure (runUnify (unifyTypes result expected))

succeedParse :: (Pretty a, Eq a) => Parser a -> Text -> a -> SpecWith ()
succeedParse parser input expected =
    describe input $
        it ("✔ parses to " <> prettyPrint expected) $
            result == expected
  where
    Right result = runParserStack parser "" input

failParse :: (Eq a) => Parser a -> Text -> SpecWith ()
failParse parser input =
    describe input $
        it "✗ fails to parse" $
            isLeft (runParserStack parser "" input)

testDatatypeParser :: SpecWith ()
testDatatypeParser = do

    succeedParse datatypeParser
        "type List a = Nil | Cons a (List a)"
        (Sum "List" ["a"] [ Mul "Nil" [] , Mul "Cons" [tVar kTyp "a", tApp kTyp (tCon kFun "List") (tVar kTyp "a")]])

    succeedParse datatypeParser
        "type User = User { name : String }"
        (Sum "User" [] [ Mul "User" [ tRecord (tRow "name" tString tRowNil) ] ])

testPatternParser :: SpecWith ()
testPatternParser = do

    succeedParse patternParser
        "x"
        (varPat () "x")

    succeedParse patternParser
        "5"
        (litPat () (TInteger 5))

    succeedParse patternParser
        "Some(x)"
        (conPat () "Some" [varPat () "x"])

    succeedParse patternParser
        "None"
        (conPat () "None" [])

    succeedParse patternParser
        "_"
        (anyPat ())

    succeedParse patternParser
        "(4, 3)"
        (tuplePat () [litPat () (TInteger 4), litPat () (TInteger 3)])

    succeedParse patternParser
        "x or 5"
        (orPat () (varPat () "x") (litPat () (TInteger 5)))

    succeedParse patternParser
        "{ x = 5 }"
        (recordPat () (rowPat () "x" (litPat () (TInteger 5)) (emptyRowPat ())))

    succeedParse patternParser
        "{ x = 5 } as y"
        (asPat () "y" (recordPat () (rowPat () "x" (litPat () (TInteger 5)) (emptyRowPat ()))))

    succeedParse patternParser
        "{}"
        (recordPat () (conPat () "{}" []))

    succeedParse patternParser
        "[1, 2]"
        (listPat () [litPat () (TInteger 1), litPat () (TInteger 2)])

    succeedParse patternParser
        "[]"
        (conPat () "[]" [])

testAnnPatternParser :: SpecWith ()
testAnnPatternParser = do

    succeedParse annPatternParser
        "x : Int"
        (annPat tInt (varPat () "x"))

    succeedParse annPatternParser
        "5 : Int"
        (annPat tInt (litPat () (TInteger 5)))

    succeedParse annPatternParser
        "_ : Int"
        (annPat tInt (anyPat ()))

    succeedParse annPatternParser
        "(4, 3) : Int"
        (annPat tInt (tuplePat () [litPat () (TInteger 4), litPat () (TInteger 3)]))

    succeedParse annPatternParser
        "(x or 5) : Int"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    succeedParse annPatternParser
        "x or 5 : Int"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    succeedParse annPatternParser
        "(x or 5 : Int)"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    succeedParse annPatternParser
        "((x or 5 : Int))"
        (annPat tInt (orPat () (varPat () "x") (litPat () (TInteger 5))))

    succeedParse annExprParser
        "let f(x : Int) = x in f"
        (letExpr () (BFun () "f" [annPat tInt (varPat () "x")]) (varExpr () "x") (varExpr () "f"))

    succeedParse annPatternParser
        "_ as x : Int"
        (annPat tInt (asPat () "x" (anyPat ())))

    succeedParse annPatternParser
        "((_ as x : Int))"
        (annPat tInt (asPat () "x" (anyPat ())))

testExprParser :: SpecWith ()
testExprParser = do

    succeedParse exprParser
        "x"
        (varExpr () "x")

    succeedParse exprParser
        "Some(x)"
        (conExpr () "Some" [varExpr () "x"])

    succeedParse exprParser
        "None"
        (conExpr () "None" [])

    succeedParse exprParser
        "(4, 3)"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    succeedParse exprParser
        "((4, 3))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    succeedParse exprParser
        "(((4, 3)))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    succeedParse exprParser
        "((((4, 3))))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    succeedParse exprParser
        "(1, 3, 4)"
        (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse exprParser
        "if (4, 3) then (1, 3, 4) else (5, 6, 7)"
        (ifExpr () 
            (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]) 
            (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)]) 
            (tupleExpr () [litExpr () (TInteger 5), litExpr () (TInteger 6), litExpr () (TInteger 7)]))

    succeedParse exprParser
        "fn(1, 3, 4)"
        (appExpr () [varExpr () "fn", litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse exprParser
        "fn (1, 3, 4)"
        (appExpr () [varExpr () "fn", litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse exprParser
        "fn(x, 3, 4)"
        (appExpr () [varExpr () "fn", varExpr () "x", litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse exprParser
        "(fn)(x, 3, 4)"
        (appExpr () [varExpr () "fn", varExpr () "x", litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse exprParser
        "(fn(x))(y)"
        (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

    succeedParse exprParser
        "[1,2,3]"
        (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3)])

    succeedParse exprParser
        "let x = (1, 2) in z"
        (letExpr () (BPat () (varPat () "x")) (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)]) (varExpr () "z"))

    succeedParse exprParser
        "let f(x) = (1, 2) in z"
        (letExpr () (BFun () "f" [varPat () "x"]) (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)]) (varExpr () "z"))

    succeedParse exprParser
        "{ x = 5 }"
        (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ())))

    succeedParse exprParser
        "{ x = { y = 5 } }"
        (recordExpr () (rowExpr () "x" (recordExpr () (rowExpr () "y" (litExpr () (TInteger 5)) (emptyRowExpr ()))) (emptyRowExpr ())))

    succeedParse exprParser
        "(x) => x"
        (lamExpr () [varPat () "x"] (varExpr () "x"))

    succeedParse exprParser
        "x => x"
        (lamExpr () [varPat () "x"] (varExpr () "x"))

    succeedParse exprParser
        "(x) => { x = 5 }"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ()))))

    succeedParse exprParser
        "x => { x = 5 }"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ()))))

    succeedParse exprParser
        "(x => { x = 5 })"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ()))))

    succeedParse exprParser
        "((x => { x = 5 }))"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ()))))

    succeedParse exprParser
        "((x) => { x = 5 })"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ()))))

    succeedParse exprParser
        "((x) => ({ x = 5 }))"
        (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TInteger 5)) (emptyRowExpr ()))))

    succeedParse exprParser
        "(x) => x + 1"
        (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))

    succeedParse exprParser
        "((x) => x + 1)(5)"
        (appExpr () 
            [ lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
            , litExpr () (TInteger 5) ])

    succeedParse exprParser
        "Some(x) => x + 1"
        (lamExpr () [conPat () "Some" [varPat () "x"]] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))

    succeedParse exprParser
        "(Some(x) => x + 1)"
        (lamExpr () [conPat () "Some" [varPat () "x"]] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))

    succeedParse exprParser
        "() => ()"
        (lamExpr () [litPat () TUnit] (litExpr () TUnit))

    succeedParse exprParser
        "let f = (x) => x + 1 in y"
        (letExpr () (BPat () (varPat () "f")) 
            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))
            (varExpr () "y"))

    succeedParse exprParser
        "let f = x => x + 1 in y"
        (letExpr () (BPat () (varPat () "f")) 
            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))
            (varExpr () "y"))

    succeedParse exprParser
        "let withDefault | Some(y) => y | None => 0 in Some(3)"
        (letExpr () (BPat () (varPat () "withDefault")) 
            (funExpr ()
                [ Clause () (conPat () "Some" [varPat () "y"]) [Guard [] (varExpr () "y")]
                , Clause () (conPat () "None" []) [Guard [] (litExpr () (TInteger 0))] 
                ])
            (conExpr () "Some" [litExpr () (TInteger 3)]))

    succeedParse exprParser
        "let withDefault(val) | Some(y) => y | None => val in Some(3)"
        (letExpr () (BFun () "withDefault" [varPat () "val"]) 
            (funExpr ()
                [ Clause () (conPat () "Some" [varPat () "y"]) [Guard [] (varExpr () "y")]
                , Clause () (conPat () "None" []) [Guard [] (varExpr () "val")] 
                ])
            (conExpr () "Some" [litExpr () (TInteger 3)]))

    succeedParse exprParser
        "{ a = True | b }"
        (recordExpr () (rowExpr () "a" (litExpr () (TBool True)) (appExpr () [varExpr () "_#", varExpr () "b"])))

    succeedParse exprParser
        "{}"
        (recordExpr () (conExpr () "{}" []))

    succeedParse exprParser
        "(x, y) => x"
        (lamExpr () [varPat () "x", varPat () "y"] (varExpr () "x")) 

    succeedParse exprParser
        "((x, y)) => x"
        (lamExpr () [tuplePat () [varPat () "x", varPat () "y"]] (varExpr () "x")) 

    succeedParse exprParser
        "(((x, y))) => x"
        (lamExpr () [tuplePat () [varPat () "x", varPat () "y"]] (varExpr () "x")) 

    succeedParse exprParser
        "[1, 2]"
        (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])

    succeedParse exprParser
        "[]"
        (conExpr () "[]" [])

    succeedParse exprParser
        "[  ]"
        (conExpr () "[]" [])

    succeedParse exprParser
        "let f() = () in f()"
        (letExpr () (BFun () "f" [litPat () TUnit]) (litExpr () TUnit) (appExpr () [varExpr () "f", litExpr () TUnit]))

    succeedParse exprParser
        "length(xs) <= 3"
        (op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3)))

    succeedParse exprParser
        "(length(xs) <= 3)"
        (op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3)))

    succeedParse exprParser
        "((length(xs) <= 3))"
        (op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3)))

    succeedParse exprParser
        "add(5, _)"
        (appExpr () [varExpr () "add", litExpr () (TInteger 5), holeExpr ()])

    succeedParse exprParser
        "add(5, _ : Int)"
        (appExpr () [varExpr () "add", litExpr () (TInteger 5), annExpr tInt (holeExpr ())])

testTypeParser :: SpecWith ()
testTypeParser = do

    succeedParseType typeParser 
        "Int"
        tInt 

    succeedParseType typeParser
        "Int -> Int"
        (tInt `tArr` tInt)

    succeedParseType typeParser 
        "List Int"
        (tList tInt)

    succeedParseType typeParser 
        "List (List Int)"
        (tApp kTyp (tCon (kArr kTyp kTyp) "List") (tApp kTyp (tCon (kArr kTyp kTyp) "List") tInt))

    succeedParseType typeParser
        "List a"
        (tApp kTyp (tCon (kArr kTyp kTyp) "List") (tVar kTyp "a"))

    succeedParseType typeParser
        "m a"
        (tApp kTyp (tVar (kArr kTyp kTyp) "m") (tVar kTyp "a"))

    succeedParseType typeParser
        "List Int -> a"
        (tApp kTyp (tCon (kArr kTyp kTyp) "List") tInt `tArr` tVar kTyp "a")

    succeedParseType typeParser
        "A B C"
        (tApp kTyp (tApp (kArr kTyp kTyp) (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tCon kTyp "B")) (tCon kTyp "C") :: Type)

    succeedParseType typeParser
        "A b c"
        (tApp kTyp (tApp (kArr kTyp kTyp) (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tVar kTyp "b")) (tVar kTyp "c") :: Type)

    succeedParseType typeParser
        "A (B C) D"
        (tApp kTyp (tApp (kArr kTyp kTyp) (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tApp kTyp (tCon (kArr kTyp kTyp) "B") (tCon kTyp "C"))) (tCon kTyp "D") :: Type)

    -- Tuple types

    succeedParseType typeParser
        "(Int, Int)"
        (tTuple [tInt, tInt])

    succeedParseType typeParser
        "(Int, a)"
        (tTuple [tInt, tVar kTyp "a"])

    -- Record types

    succeedParseType typeParser
        "{ a : Int }"
        (tRecord (tRow "a" tInt tRowNil))

    succeedParseType typeParser
        "{ a : Int, b : a }"
        (tRecord (tRow "a" tInt (tRow "b" (tVar kTyp "a") tRowNil)))

    succeedParseType typeParser
        "{ a : Int, b : a | c }"
        (tRecord (tRow "a" tInt (tRow "b" (tVar kTyp "a") (tVar kRow "c"))))

    succeedParseType typeParser
        "{}"
        (tRecord tRowNil)

testExprParserMatch :: SpecWith ()
testExprParserMatch = do

    succeedParse exprParser
        "match x with | 4 => { a = 5 }"
        (patExpr () (varExpr () "x") 
            [ Clause () (litPat () (TInteger 4)) 
                  [ Guard [] (recordExpr () (rowExpr () "a" (litExpr () (TInteger 5)) (emptyRowExpr ()))) ]
            ])

    succeedParse exprParser
        "match x with | 4 => { a = 5 } | 5 => { a = 7 }"
        (patExpr () (varExpr () "x") 
            [ Clause () (litPat () (TInteger 4)) 
                  [ Guard [] (recordExpr () (rowExpr () "a" (litExpr () (TInteger 5)) (emptyRowExpr ()))) ]
            , Clause () (litPat () (TInteger 5)) 
                  [ Guard [] (recordExpr () (rowExpr () "a" (litExpr () (TInteger 7)) (emptyRowExpr ()))) ]
            ])

--    succeedParse exprParser
--        "match x with | y when y > 5 => True"
--        (patExpr () (varExpr () "x") 
--            [ Clause () (varPat () "y") 
--                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5))] (litExpr () (TBool True)) ]
--            ])

    succeedParse exprParser
        "match x with | y when(y > 5) => True"
        (patExpr () (varExpr () "x") 
            [ Clause () (varPat () "y") 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5))] (litExpr () (TBool True)) ]
            ])

--    succeedParse exprParser
--        "match x with | y when y > 5 => 0 when y > 1 => 1 otherwise => 2"
--        (patExpr () (varExpr () "x") 
--            [ Clause () (varPat () "y") 
--                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5))] (litExpr () (TInteger 0)) 
--                  , Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) 
--                  , Guard [] (litExpr () (TInteger 2)) 
--                  ]
--            ])

    succeedParse exprParser
        "match x with | y when(y > 5, z > 2) => True"
        (patExpr () (varExpr () "x") 
            [ Clause () (varPat () "y") 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5)), op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 2))] (litExpr () (TBool True)) ]
            ])

    succeedParse exprParser
        "match x with | y when(y > 5) => 0 when(y > 1) => 1 otherwise => 2"
        (patExpr () (varExpr () "x") 
            [ Clause () (varPat () "y") 
                  [ Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 5))] (litExpr () (TInteger 0)) 
                  , Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) 
                  , Guard [] (litExpr () (TInteger 2)) 
                  ]
            ])

    succeedParse exprParser
        "x.f"
        (op2Expr () (ODot ()) (varExpr () "f") (varExpr () "x"))

    succeedParse exprParser
        "xs.map(f)"
        (op2Expr () (ODot ()) (appExpr () [varExpr () "map", varExpr () "f"]) (varExpr () "xs"))

    succeedParse exprParser
        "xs.map((x) => x + 1)"
        (op2Expr () (ODot ()) (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))]) (varExpr () "xs"))

    succeedParse exprParser
        "xs.map(x => x + 1)"
        (op2Expr () (ODot ()) (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))]) (varExpr () "xs"))

    succeedParse exprParser
        "{ a = { b = \"c\" } }.a.b"
        (Fix (EOp2 () (ODot ()) (Fix (EVar () "b")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "a")) (Fix (ECon () "#" [Fix (ERow () "a" (Fix (ECon () "#" [Fix (ERow () "b" (Fix (ELit () (TString "c"))) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))]))))))

testAnnExprParser :: SpecWith ()
testAnnExprParser = do

    failParse annExprParser "!5"

    succeedParse annExprParser
        "4"
        (litExpr () (TInteger 4))

    succeedParse annExprParser
        "4 : Int"
        (annExpr tInt (litExpr () (TInteger 4)))

    succeedParse annExprParser
        "(4 : Int)"
        (annExpr tInt (litExpr () (TInteger 4)))

    succeedParse annExprParser
        "(4)"
        (litExpr () (TInteger 4))

    succeedParse annExprParser
        "((4))"
        (litExpr () (TInteger 4))

    succeedParse annExprParser
        "((4) : Int)"
        (annExpr tInt (litExpr () (TInteger 4)))

    succeedParse annExprParser
        "(4) : Int"
        (annExpr tInt (litExpr () (TInteger 4)))

    succeedParse annExprParser
        "((4, 3) : Int)"
        (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))

    succeedParse annExprParser
        "(((4, 3)))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    succeedParse annExprParser
        "((((4, 3))))"
        (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)])

    failParse annExprParser
        "((((4, 3)]]]"

    succeedParse annExprParser
        "(((4, 3) : Int))"
        (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))

    succeedParse annExprParser
        "(4, 3) : Int"
        (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))

    succeedParse annExprParser
        "if (4, 3) : Int then (1, 3, 4) else (5, 6, 7)"
        (ifExpr () 
            (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))
            (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)]) 
            (tupleExpr () [litExpr () (TInteger 5), litExpr () (TInteger 6), litExpr () (TInteger 7)]))

    succeedParse annExprParser
        "(if (4, 3) : Int then (1, 3, 4) else (5, 6, 7)) : Int"
        (annExpr tInt (ifExpr () 
            (annExpr tInt (tupleExpr () [litExpr () (TInteger 4), litExpr () (TInteger 3)]))
            (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 3), litExpr () (TInteger 4)]) 
            (tupleExpr () [litExpr () (TInteger 5), litExpr () (TInteger 6), litExpr () (TInteger 7)])))

    succeedParse annExprParser
        "fn(1 : Int, 3, 4)"
        (appExpr () [varExpr () "fn", annExpr tInt (litExpr () (TInteger 1)), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse annExprParser
        "fn(1 : Int, 3, 4) : Int"
        (annExpr tInt (appExpr () [varExpr () "fn", annExpr tInt (litExpr () (TInteger 1)), litExpr () (TInteger 3), litExpr () (TInteger 4)]))

    succeedParse annExprParser
        "fn(x : Int, 3, 4)"
        (appExpr () [varExpr () "fn", annExpr tInt (varExpr () "x"), litExpr () (TInteger 3), litExpr () (TInteger 4)])

    succeedParse annExprParser
        "((fn(x))(y))"
        (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

    succeedParse exprParser
        "[1 : Int, 2, 3]"
        (listExpr () [annExpr tInt (litExpr () (TInteger 1)), litExpr () (TInteger 2), litExpr () (TInteger 3)])

    succeedParse exprParser
        "let x = (1, 2) : Int in z"
        (letExpr () (BPat () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])) (varExpr () "z"))

    succeedParse exprParser
        "let x = (1, 2) : Int in z : Int"
        (letExpr () (BPat () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])) (annExpr tInt (varExpr () "z")))

    succeedParse annExprParser
        "(let x = (1, 2) : Int in z : Int) : Int"
        (annExpr tInt (letExpr () (BPat () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2)])) (annExpr tInt (varExpr () "z"))))

    succeedParse annExprParser
        "{ x = 5 : Int }"
        (recordExpr () (rowExpr () "x" (annExpr tInt (litExpr () (TInteger 5))) (emptyRowExpr ())))

    succeedParse annExprParser
        "(x : Int) => x + 1"
        (lamExpr () [annPat tInt (varPat () "x")] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))

    succeedParse annExprParser
        "x : Int => x + 1"
        (lamExpr () [annPat tInt (varPat () "x")] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))
