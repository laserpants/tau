{-# LANGUAGE OverloadedStrings #-}
module Tau.ParserTests where

import Data.Either
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Pretty
import Tau.Lang.Type
import Test.Hspec
import Text.Megaparsec hiding (ParseError)
import Utils

succeedParse :: (Eq p, Pretty p) => Parser p -> Text -> Text -> p -> SpecWith ()
succeedParse parser what input expect = 
    describe (unpack input) $ do
        let result = parseWith parser input

        it ("✔ succeeds to parse to " <> unpack what) $
            isRight result

        it ("✔ and gives the expected result: " <> prettyString expect) $
            Right expect == result

failParse :: Parser p -> Text -> Text -> SpecWith ()
failParse parser what input = 
    describe (unpack input) $ do
        let result = parseWith parser input

        it ("✗ fails to parse to " <> unpack what) $
            isLeft result

parseWith :: Parser p -> Text -> Either ParseError p
parseWith parser = runParser parser ""

testParser :: SpecWith ()
testParser = do

    -- Identifiers 

    succeedParse name "an identifier"
        "yeah" 
        "yeah"

    succeedParse name "an identifier"
        "_yeah" 
        "_yeah"

    failParse name "an identifier"
        "Nay" 

    failParse name "an identifier"
        "*foo" 

    failParse name "an identifier"
        "" 

    failParse name "an identifier"
        "let" 

    -- Constructors

    succeedParse constructor_ "a constructor" 
        "Hello" 
        "Hello"

    failParse constructor_ "a constructor" 
        "hello"
    
    failParse constructor_ "a constructor" 
        "False"

    -- Kinds

    succeedParse kind "a kind"
        "* -> * -> *"
        (kArr kTyp (kArr kTyp kTyp))

    succeedParse kind "a kind"
        "* -> (* -> *)"
        (kArr kTyp (kArr kTyp kTyp))

    succeedParse kind "a kind"
        "(* -> *) -> *"
        (kArr (kArr kTyp kTyp) kTyp)

    -- Literals

    succeedParse charLit "a Char"
        "'x'"
        (LChar 'x')

    failParse charLit "a Char"
        "x"

    succeedParse bool "a Bool"
        "True"
        (LBool True)

    succeedParse bool "a Bool"
        "False"
        (LBool False)

    failParse bool "a Bool"
        "false"

    failParse bool "a Bool"
        "Falsetto"

    succeedParse float "a Float"
        "3.14"
        (LFloat 3.14)

    succeedParse integral "an Int"
        "3"
        (LInt 3)

    succeedParse stringLit "a String"
        "\"pasta\""
        (LString "pasta")

    failParse stringLit "a String"
        "pasta\""

    succeedParse stringLit "a String"
        "\"\""
        (LString "")

    succeedParse unit "a Unit value"
        "()"
        LUnit

    -- Patterns

    succeedParse pattern_ "a pattern"
        "Some X"
        (conPat () "Some" [conPat () "X" []])

    succeedParse pattern_ "a pattern"
        "5"
        (litPat () (LInt 5))

    succeedParse pattern_ "a pattern"
        "Some (Some X)"
        (conPat () "Some" [conPat () "Some" [conPat () "X" []]])

    succeedParse pattern_ "a pattern"
        "x :: xs"
        (conPat () "(::)" [varPat () "x", varPat () "xs"])

    succeedParse pattern_ "a pattern"
        "(x, y)"
        (tupPat () [varPat () "x", varPat () "y"])

    succeedParse pattern_ "a pattern"
        "{ a = x }"
        (recPat () (fieldSet [Field () "a" (varPat () "x")]))

    succeedParse pattern_ "a pattern"
        "(1, x) or (x, 1)"
        (orPat () (tupPat () [litPat () (LInt 1), varPat () "x"]) (tupPat () [varPat () "x", litPat () (LInt 1)])) 

    succeedParse pattern_ "a pattern"
        "(1, x) as pair"
        (asPat () "pair" (tupPat () [litPat () (LInt 1), varPat () "x"])) 
