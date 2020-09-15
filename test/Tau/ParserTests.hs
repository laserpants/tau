{-# LANGUAGE OverloadedStrings #-}
module Tau.ParserTests where

import Data.Either
import Tau.Expr
import Tau.Parser
import Test.Hspec
import Utils

failParse :: Text -> SpecWith ()
failParse input =
    describe (unpack input) $ do
        let result = parseExpr input

        it "✗ fails to parse" $
            isLeft result 

succeedParse :: Text -> Expr -> SpecWith ()
succeedParse input expect = 
    describe (unpack input) $ do
        let result = parseExpr input

        it "✔ succeeds to parse" $
            isRight result 

        it ("✔ and gives the expected result: " <> prettyString expect) $
            Right expect == result

bigNumber :: Integer
bigNumber = (fromIntegral (maxBound :: Int) :: Integer) + 1

testParser :: SpecWith ()
testParser = do
    succeedParse
        "4.3"
        (litFloat 4.3)

    succeedParse
        "4"
        (litInt 4)

    succeedParse
        "let x = 3 in x"
        (letS "x" (litInt 3) (varS "x"))

    succeedParse
        "f x"
        (appS [varS "f", varS "x"])

    succeedParse
        "x"
        (varS "x")

    succeedParse
        "f (g y)"
        (appS [varS "f", appS [varS "g", varS "y"]])
    
    succeedParse
        "f g h i"
        (appS (varS <$> ["f", "g", "h", "i"]))

    succeedParse
        "()"
        litUnit

    succeedParse
        "(())"
        litUnit

    succeedParse
        "match n with 1 => True | 2 => False"
        (matchS (varS "n") [(litP (Int 1), litBool True), (litP (Int 2), litBool False)])

    succeedParse
        "match n with | 1 => True | 2 => False"
        (matchS (varS "n") [(litP (Int 1), litBool True), (litP (Int 2), litBool False)])

    succeedParse
        "let rec map = \\f => \\xs => match xs with Nil => Nil | Cons x1 xs1 => Cons (f x1) (map f xs1) in map"
        (recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], varS "Nil"), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (varS "map"))

    succeedParse
        "let rec map = \\f => \\xs => match xs | Nil => Nil | Cons x1 xs1 => Cons (f x1) (map f xs1) in map (\\x => x == 0)"
        (recS "map" (lamS "f" (lamS "xs" (matchS (varS "xs") [(conP "Nil" [], varS "Nil"), (conP "Cons" [varP "x1", varP "xs1"], appS [varS "Cons", appS [varS "f", varS "x1"], appS [varS "map", varS "f", varS "xs1"]])]))) (appS [varS "map", lamS "x" (eqS (varS "x") (litInt 0))]))

    succeedParse
        "let str = \"hello\" in str"
        (letS "str" (litString "hello") (varS "str"))

    succeedParse
        "\"hello\" == \"what\""
        (eqS (litString "hello") (litString "what"))

    succeedParse
        "\"hello\""
        (litString "hello")

    succeedParse
        "'a' == 'b'"
        (eqS (litChar 'a') (litChar 'b'))

    succeedParse
        "let chr = 'a' in chr == chr"
        (letS "chr" (litChar 'a') (eqS (varS "chr") (varS "chr")))

    succeedParse
        "(\\match | (Cons x (Cons y ys)) => 4) Nil"
        (appS [lamMatchS [(conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]], litInt 4)], varS "Nil"])

    succeedParse
        "(\\match Cons x (Cons y ys) => 4) Nil"
        (appS [lamMatchS [(conP "Cons" [varP "x", conP "Cons" [varP "y", varP "ys"]], litInt 4)], varS "Nil"])

    succeedParse
        "123"
        (litInt 123)

    succeedParse
        (pack (show bigNumber))
        (litInteger bigNumber)

    failParse "let chr = let in x"
