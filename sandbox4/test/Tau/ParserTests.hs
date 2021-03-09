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
        "_"
        (anyPat ())

    succeedParse pattern_ "a pattern"
        "x"
        (varPat () "x")

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

    -- Types

    succeedParse type_ "a type"
        "Int"
        (tInt :: Type)

    succeedParse type_ "a type"
        "List Int"
        (tApp (tCon (kArr kTyp kTyp) "List") tInt :: Type)

    succeedParse type_ "a type"
        "List (List Int)"
        (tApp (tCon (kArr kTyp kTyp) "List") (tApp (tCon (kArr kTyp kTyp) "List") tInt) :: Type)

    succeedParse type_ "a type"
        "List a"
        (tApp (tCon (kArr kTyp kTyp) "List") (tVar kTyp "a") :: Type)

    succeedParse type_ "a type"
        "m a"
        (tApp (tVar (kArr kTyp kTyp) "m") (tVar kTyp "a") :: Type)

    succeedParse type_ "a type"
        "List Int -> a"
        (tApp (tCon (kArr kTyp kTyp) "List") tInt `tArr` tVar kTyp "a" :: Type)

    --  Expressions

    describe "\nlet expressions\n" $ do

        succeedParse expr "an expression"
            "let f x y = z in a"
            (letExpr () (BFun "f" [varPat () "x", varPat () "y"]) (varExpr () "z") (varExpr () "a"))

        succeedParse expr "an expression"
            "let f (Some x) y = z in a"
            (letExpr () (BFun "f" [conPat () "Some" [varPat () "x"], varPat () "y"]) (varExpr () "z") (varExpr () "a"))

        succeedParse expr "an expression"
            "let f y (Some x) = z in a"
            (letExpr () (BFun "f" [varPat () "y", conPat () "Some" [varPat () "x"]]) (varExpr () "z") (varExpr () "a"))

        succeedParse expr "an expression"
            "let f (Some x as someX) y = z in a"
            (letExpr () (BFun "f" [asPat () "someX" (conPat () "Some" [varPat () "x"]), varPat () "y"]) (varExpr () "z") (varExpr () "a"))

        succeedParse expr "an expression"
            "let x = z in a"
            (letExpr () (BLet (varPat () "x")) (varExpr () "z") (varExpr () "a"))

    describe "\nlambdas\n" $ do

        succeedParse expr "an expression"
            "\\f x => f x"
            (lamExpr () [varPat () "f", varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))

    describe "\nliterals\n" $ do

        succeedParse expr "an expression"
            "3.14"
            (litExpr () (LFloat 3.14))

    describe "\nmatch expressions\n" $ do

        succeedParse expr "an expression"
            "match xs with | (y :: ys) => y"
            (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "y")])

        succeedParse expr "an expression"
            "match xs with | (5 :: ys) => True"
            (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [litPat () (LInt 5), varPat () "ys"]] [] (litExpr () (LBool True))])

        succeedParse expr "an expression"
            "match xs with | (y :: ys) when y > 5 => True"
            (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (LInt 5))] (litExpr () (LBool True))])

        succeedParse expr "an expression"
            "match xs with | (y :: ys) when y > 5 => True | _ => False"
            (patExpr () [varExpr () "xs"] 
                [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (LInt 5))] (litExpr () (LBool True)) 
                , Clause [anyPat ()] [] (litExpr () (LBool False)) ])

    describe "\nlists\n" $ do

        succeedParse expr "an expression"
            "[]"
            (conExpr () "[]" [])

        succeedParse expr "an expression"
            "1 :: 2 :: 3 :: []"
            (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]])

        succeedParse expr "an expression"
            "[1,2,3]"
            (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]])

    describe "\ntuples\n" $ do

        succeedParse expr "an expression"
            "(1, 2)"
            (tupExpr () [litExpr () (LInt 1), litExpr () (LInt 2)])

    describe "\nrecords\n" $ do

        succeedParse expr "an expression"
            "{ name = \"Sun Ra\", style = \"Avant Garde\" }"
            (recExpr () (fieldSet [ Field () "name" (litExpr () (LString "Sun Ra")), Field () "style" (litExpr () (LString "Avant Garde"))]))

        succeedParse expr "an expression"
            "{ user = { id = 1, name = \"Alfred Hitchcock\" } }"
            (recExpr () (fieldSet [ Field () "user" (recExpr () (fieldSet [ Field () "id" (litExpr () (LInt 1)), Field () "name" (litExpr () (LString "Alfred Hitchcock")) ])) ]))

    describe "\nfunction application\n" $ do

        succeedParse expr "an expression"
            "a b c"
            (appExpr () [varExpr () "a", varExpr () "b", varExpr () "c"])

        succeedParse expr "an expression"
            "a (b c)"
            (appExpr () [varExpr () "a", appExpr () [varExpr () "b", varExpr () "c"]])

        succeedParse expr "an expression"
            "(\\xs => match xs with | (x :: xs) => x) [1,2,3]"
            (appExpr () [lamExpr () [varPat () "xs"] (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")]), conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

    describe "\nmixed expressions\n" $ do

        succeedParse expr "an expression"
            "(fun | (x :: xs) => x) [1,2,3]"
            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

        succeedParse expr "an expression"
            "(fun (x :: xs) => x) [1,2,3]"
            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

        succeedParse expr "an expression"
            "(fun x :: xs => x) [1,2,3]"
            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

    --  Operators

    describe "\noperators\n" $ do

        succeedParse expr "an expression"
            "x + y"
            (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y"))

        succeedParse expr "an expression"
            "xs.length"
            (dotExpr () "length" (varExpr () "xs"))

        succeedParse expr "an expression"
            "xs.length.toString"
            (dotExpr () "toString" (dotExpr () "length" (varExpr () "xs")))

--        succeedParse expr "an expression"
--            "xs.map (\x => x + 1)"

