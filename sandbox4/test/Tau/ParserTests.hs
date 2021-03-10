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

        it ("✔ and it is the expected result: " <> prettyString expect <> "\n") $
            Right expect == result

failParse :: Parser p -> Text -> Text -> SpecWith ()
failParse parser what input = 
    describe (if "" == input then "\"\"" else unpack input) $ do
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
        "[]"
        (conPat () "[]" [])

    succeedParse pattern_ "a pattern"
        "[1, x]"
        (conPat () "(::)" [litPat () (LInt 1), conPat () "(::)" [varPat () "x", conPat () "[]" []]])

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

    succeedParse pattern_ "a pattern"
        "1 or 2 or 3"
        (orPat () (litPat () (LInt 1)) (orPat () (litPat () (LInt 2)) (litPat () (LInt 3))))

    succeedParse pattern_ "a pattern"
        "1 or 2 :: xs"
        (conPat () "(::)" [orPat () (litPat () (LInt 1)) (litPat () (LInt 2)), varPat () "xs"])

    succeedParse pattern_ "a pattern"
        "1 or 2 or 3 :: xs"
        (conPat () "(::)" [orPat () (litPat () (LInt 1)) (orPat () (litPat () (LInt 2)) (litPat () (LInt 3))), varPat () "xs"])

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

    describe "\nLet expressions\n" $ do

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

    describe "\nLambdas\n" $ do

        succeedParse expr "an expression"
            "\\f x => f x"
            (lamExpr () [varPat () "f", varPat () "x"] (appExpr () [varExpr () "f", varExpr () "x"]))

    describe "\nLiterals\n" $ do

        succeedParse expr "an expression"
            "3.14"
            (litExpr () (LFloat 3.14))

    describe "\nMatch expressions\n" $ do

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

    describe "\nLists\n" $ do

        succeedParse expr "an expression"
            "[]"
            (conExpr () "[]" [])

        succeedParse expr "an expression"
            "1 :: 2 :: 3 :: []"
            (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]])

        succeedParse expr "an expression"
            "[1,2,3]"
            (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]])

    describe "\nTuples\n" $ do

        succeedParse expr "an expression"
            "(1, 2)"
            (tupExpr () [litExpr () (LInt 1), litExpr () (LInt 2)])

    describe "\nRecords\n" $ do

        succeedParse expr "an expression"
            "{ name = \"Sun Ra\", style = \"Avant Garde\" }"
            (recExpr () (fieldSet [ Field () "name" (litExpr () (LString "Sun Ra")), Field () "style" (litExpr () (LString "Avant Garde"))]))

        succeedParse expr "an expression"
            "{ user = { id = 1, name = \"Alfred Hitchcock\" } }"
            (recExpr () (fieldSet [ Field () "user" (recExpr () (fieldSet [ Field () "id" (litExpr () (LInt 1)), Field () "name" (litExpr () (LString "Alfred Hitchcock")) ])) ]))

    describe "\nFunction application\n" $ do

        succeedParse expr "an expression"
            "a b c"
            (appExpr () [varExpr () "a", varExpr () "b", varExpr () "c"])

        succeedParse expr "an expression"
            "a (b c)"
            (appExpr () [varExpr () "a", appExpr () [varExpr () "b", varExpr () "c"]])

        succeedParse expr "an expression"
            "(\\xs => match xs with | (x :: xs) => x) [1,2,3]"
            (appExpr () [lamExpr () [varPat () "xs"] (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")]), conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

    describe "\nConstructors\n" $ do

        succeedParse expr "an expression"
            "Some x"
            (conExpr () "Some" [varExpr () "x"])
            
        succeedParse expr "an expression"
            "None"
            (conExpr () "None" [])

    --  Mixed expressions

    describe "\nMixed expressions\n" $ do

        succeedParse expr "an expression"
            "(fun | (x :: xs) => x) [1,2,3]"
            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

        succeedParse expr "an expression"
            "(fun (x :: xs) => x) [1,2,3]"
            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

        succeedParse expr "an expression"
            "(fun x :: xs => x) [1,2,3]"
            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]])

        succeedParse expr "an expression"
            "fun [] => [] | y :: ys => f y :: mu ys"
            (patExpr () [] [Clause [conPat () "[]" []] [] (conExpr () "[]" []), Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "y"], appExpr () [varExpr () "mu", varExpr () "ys"]])])

        succeedParse expr "an expression"
            "letfix mu = fun [] => [] | y :: ys => f y :: mu ys in mu xs"
            (fixExpr () "mu" (patExpr () [] 
                [ Clause [conPat () "[]" []] [] (conExpr () "[]" [])
                , Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "y"], appExpr () [varExpr () "mu", varExpr () "ys"]])
                ]) (appExpr () [varExpr () "mu", varExpr () "xs"]))

        succeedParse expr "an expression"
            "let map f xs = letfix mu = fun [] => [] | y :: ys => f y :: mu ys in mu xs in let xs = [1, 2, 3] in xs.map (\\x => x + 1)"
            (letExpr () (BFun "map" [varPat () "f", varPat () "xs"]) (fixExpr () "mu" (patExpr () [] 
                [ Clause [conPat () "[]" []] [] (conExpr () "[]" [])
                , Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "y"], appExpr () [varExpr () "mu", varExpr () "ys"]])
                ]) (appExpr () [varExpr () "mu", varExpr () "xs"])) (letExpr () (BLet (varPat () "xs")) (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]) (dotExpr () (varExpr () "xs") (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (LInt 1)))]))))

        succeedParse expr "an expression"
            "letfix len = fun [] => 0 | x :: xs => 1 + len xs in [].len"
            (fixExpr () "len" (patExpr () [] [Clause [conPat () "[]" []] [] (litExpr () (LInt 0)), Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (op2Expr () (OAdd ()) (litExpr () (LInt 1)) (appExpr () [varExpr () "len", varExpr () "xs"]))]) (dotExpr () (conExpr () "[]" []) (varExpr () "len")))

        succeedParse expr "an expression"
            "letfix len = fun [] => 0 | x :: xs => 1 + len xs in [1,2,3,4,5].len"
            (fixExpr () "len" (patExpr () [] [Clause [conPat () "[]" []] [] (litExpr () (LInt 0)), Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (op2Expr () (OAdd ()) (litExpr () (LInt 1)) (appExpr () [varExpr () "len", varExpr () "xs"]))]) (dotExpr () (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "(::)" [litExpr () (LInt 4), conExpr () "(::)" [litExpr () (LInt 5), conExpr () "[]" []]]]]]) (varExpr () "len")))

        succeedParse expr "an expression"
            "let first (a, b) = a in (5, ()).first"
            (letExpr () (BFun "first" [tupPat () [varPat () "a", varPat () "b"]]) (varExpr () "a") (dotExpr () (tupExpr () [litExpr () (LInt 5), litExpr () LUnit]) (varExpr () "first")))

        succeedParse expr "an expression"
            "f a (b.length)"
            (appExpr () [varExpr () "f", varExpr () "a", dotExpr () (varExpr () "b") (varExpr () "length")])

        succeedParse expr "an expression"
            "f a b.length"
            (appExpr () [varExpr () "f", varExpr () "a", dotExpr () (varExpr () "b") (varExpr () "length")])

        succeedParse expr "an expression"
            "withDefault 0 [1,2,3].head"
            (appExpr () [varExpr () "withDefault", litExpr () (LInt 0), dotExpr () (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]) (varExpr () "head")])

        -- let withDefault(default) = fun 
        --   | None       => default
        --   | Some value => value 
        -- in 
        --   let head = fun 
        --     | []     => None 
        --     | x :: _ => Some x 
        --   in 
        --     withDefault 0 [1,2,3].head"

        succeedParse expr "an expression"
            "let withDefault default = fun None => default | Some value => value in let head = fun [] => None | x :: _ => Some x in withDefault 0 [1,2,3].head"
            (letExpr () (BFun "withDefault" [varPat () "default"]) (patExpr () [] [Clause [conPat () "None" []] [] (varExpr () "default"), Clause [conPat () "Some" [varPat () "value"]] [] (varExpr () "value")])
                (letExpr () (BLet (varPat () "head")) (patExpr () [] [Clause [conPat () "[]" []] [] (conExpr () "None" []), Clause [conPat () "(::)" [varPat () "x", anyPat ()]] [] (conExpr () "Some" [varExpr () "x"])])
                    (appExpr () [varExpr () "withDefault", litExpr () (LInt 0), dotExpr () (conExpr () "(::)" [litExpr () (LInt 1), conExpr () "(::)" [litExpr () (LInt 2), conExpr () "(::)" [litExpr () (LInt 3), conExpr () "[]" []]]]) (varExpr () "head")])))

        -- let withDefault(default) = \None => default | Some value => value 
        -- in 
        --   let head = fun 
        --     | []     => None 
        --     | x :: _ => Some x 
        --   in 
        --     withDefault 0 [1,2,3].head"

    --  Operators

    describe "\nOperators\n" $ do

        succeedParse expr "an expression"
            "x + y"
            (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y"))

        -- Addition associativity

        succeedParse expr "an expression"
            "x + y + z"
            (op2Expr () (OAdd ()) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (varExpr () "z"))

        -- Operator precedence

        succeedParse expr "an expression"
            "x * y + z"
            (op2Expr () (OAdd ()) (op2Expr () (OMul ()) (varExpr () "x") (varExpr () "y")) (varExpr () "z"))

        succeedParse expr "an expression"
            "xs.length"
            (dotExpr () (varExpr () "xs") (varExpr () "length"))

        succeedParse expr "an expression"
            "xs.length.toString"
            (dotExpr () (dotExpr () (varExpr () "xs") (varExpr () "length")) (varExpr () "toString"))

        succeedParse expr "an expression"
            "xs.map (\\x => x + 1)"
            (dotExpr () (varExpr () "xs") (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (LInt 1)))]))

