{-# LANGUAGE OverloadedStrings #-}
module Tau.ParserTests where

import Data.Either
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Pretty
import Tau.Lang.Prog
import Tau.Lang.Type
import Test.Hspec
import Text.Megaparsec hiding (ParseError)
import Utils

succeedParse :: (Eq p, Pretty p) => Parser p -> Text -> Text -> p -> SpecWith ()
succeedParse parser what input expect = 
    describe ("\n" <> unpack input <> "\n") $ do
        let result = parseWith parser input

        it ("✔ succeeds to parse to " <> unpack what) $
            isRight result

        it ("✔ and it is the expected result: " <> prettyString expect <> "\n") $
            Right expect == result

failParse :: Parser p -> Text -> Text -> SpecWith ()
failParse parser what input = 
    describe (if "" == input then "\"\"" else "\n" <> unpack input <> "\n") $ do
        let result = parseWith parser input

        it ("✗ fails to parse to " <> unpack what <> "\n") $
            isLeft result

parseWith :: Parser p -> Text -> Either ParseError p
parseWith parser = runParser parser ""

testParser :: SpecWith ()
testParser = do

    -- Identifiers 

    describe "\nIdentifiers\n" $ do

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

    describe "\nConstructors\n" $ do

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

    succeedParse charLit "a Char literal"
        "'x'"
        (TChar 'x')

    failParse charLit "a Char literal"
        "x"

    succeedParse bool "a Bool literal"
        "True"
        (TBool True)

    succeedParse bool "a Bool literal"
        "False"
        (TBool False)

    failParse bool "a Bool literal"
        "false"

    failParse bool "a Bool literal"
        "Falsetto"

    succeedParse float "a Float literal"
        "3.14"
        (TFloat 3.14)

    succeedParse integral "an Int literal"
        "3"
        (TInt 3)

    succeedParse stringLit "a String literal"
        "\"pasta\""
        (TString "pasta")

    failParse stringLit "a String literal"
        "pasta\""

    succeedParse stringLit "a String literal"
        "\"\""
        (TString "")

    succeedParse unit "a Unit literal"
        "()"
        TUnit

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
        "A B C"
        (conPat () "A" [conPat () "B" [], conPat () "C" []])

    succeedParse pattern_ "a pattern"
        "A b c"
        (conPat () "A" [varPat () "b", varPat () "c"])

    succeedParse pattern_ "a pattern"
        "A (B C) D"
        (conPat () "A" [conPat () "B" [conPat () "C" []], conPat () "D" []])

    succeedParse pattern_ "a pattern"
        "5"
        (litPat () (TInt 5))

    succeedParse pattern_ "a pattern"
        "[]"
        (lstPat () [])

    succeedParse pattern_ "a pattern"
        "[1, x]"
        (lstPat () [litPat () (TInt 1), varPat () "x"])

    succeedParse pattern_ "a pattern"
        "[[x]]"
        (lstPat () [lstPat () [varPat () "x"]])

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
        (orPat () (tupPat () [litPat () (TInt 1), varPat () "x"]) (tupPat () [varPat () "x", litPat () (TInt 1)])) 

    succeedParse pattern_ "a pattern"
        "(1, x) as pair"
        (asPat () "pair" (tupPat () [litPat () (TInt 1), varPat () "x"])) 

    succeedParse pattern_ "a pattern"
        "1 or 2 or 3"
        (orPat () (litPat () (TInt 1)) (orPat () (litPat () (TInt 2)) (litPat () (TInt 3))))

    succeedParse pattern_ "a pattern"
        "1 or 2 :: xs"
        (conPat () "(::)" [orPat () (litPat () (TInt 1)) (litPat () (TInt 2)), varPat () "xs"])

    succeedParse pattern_ "a pattern"
        "1 or 2 or 3 :: xs"
        (conPat () "(::)" [orPat () (litPat () (TInt 1)) (orPat () (litPat () (TInt 2)) (litPat () (TInt 3))), varPat () "xs"])

    -- Types

    describe "\nTypes\n" $ do

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

        succeedParse type_ "an expression"
            "A B C"
            (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tCon kTyp "B")) (tCon kTyp "C") :: Type)

        succeedParse type_ "an expression"
            "A b c"
            (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tVar kTyp "b")) (tVar kTyp "c") :: Type)

        succeedParse type_ "an exprssion"
            "A (B C) D"
            (tApp (tApp (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tApp (tCon (kArr kTyp kTyp) "B") (tCon kTyp "C"))) (tCon kTyp "D") :: Type)

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

        succeedParse expr "an expression"
            "\\f x => [x]"
            (lamExpr () [varPat () "f", varPat () "x"] (lstExpr () [varExpr () "x"]))

    describe "\nLiterals\n" $ do

        succeedParse expr "an expression"
            "3.14"
            (litExpr () (TFloat 3.14))

    describe "\nMatch expressions\n" $ do

        succeedParse expr "an expression"
            "match xs with | (y :: ys) => y"
            (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [] (varExpr () "y")]])
            --(patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (varExpr () "y")])

        succeedParse expr "an expression"
            "match xs with | (5 :: ys) => True"
            (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [litPat () (TInt 5), varPat () "ys"]] [Guard [] (litExpr () (TBool True))]])
            --(patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [litPat () (TInt 5), varPat () "ys"]] [] (litExpr () (TBool True))])

        succeedParse expr "an expression"
            "match xs with | (y :: ys) when y > 5 => True"
            (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInt 5))] (litExpr () (TBool True))]])
            --(patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInt 5))] (litExpr () (TBool True))])

        succeedParse expr "an expression"
            "match xs with | (y :: ys) when y > 5 => True | _ => False"
            (patExpr () [varExpr () "xs"] 
                [ Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [Guard [op2Expr () (OGt ()) (varExpr () "y") (litExpr () (TInt 5))] (litExpr () (TBool True))] 
                , Clause [anyPat ()] [Guard [] (litExpr () (TBool False))] ])

    describe "\nLists\n" $ do

        succeedParse expr "an expression"
            "[]"
            (lstExpr () [])

--        succeedParse expr "an expression"
--            "1 :: 2 :: 3 :: []"
--            (conExpr () "(::)" [litExpr () (TInt 1), conExpr () "(::)" [litExpr () (TInt 2), conExpr () "(::)" [litExpr () (TInt 3), lstExpr () []]]])
--
--        succeedParse expr "an expression"
--            "[1,2,3]"
--            (lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)])
--
--        succeedParse expr "an expression"
--            "[()]"
--            (lstExpr () [litExpr () TUnit])
--
--    describe "\nTuples\n" $ do
--
--        succeedParse expr "an expression"
--            "(1, 2)"
--            (tupExpr () [litExpr () (TInt 1), litExpr () (TInt 2)])
--
--        succeedParse expr "an expression"
--            "([1], 2)"
--            (tupExpr () [lstExpr () [litExpr () (TInt 1)], litExpr () (TInt 2)])
--
--    describe "\nRecords\n" $ do
--
--        succeedParse expr "an expression"
--            "{ name = \"Sun Ra\", style = \"Avant Garde\" }"
--            (recExpr () (fieldSet [ Field () "name" (litExpr () (TString "Sun Ra")), Field () "style" (litExpr () (TString "Avant Garde"))]))
--
--        succeedParse expr "an expression"
--            "{ user = { id = 1, name = \"Alfred Hitchcock\" } }"
--            (recExpr () (fieldSet [ Field () "user" (recExpr () (fieldSet [ Field () "id" (litExpr () (TInt 1)), Field () "name" (litExpr () (TString "Alfred Hitchcock")) ])) ]))
--
--    describe "\nFunction application\n" $ do
--
--        succeedParse expr "an expression"
--            "a b c"
--            (appExpr () [varExpr () "a", varExpr () "b", varExpr () "c"])
--
--        succeedParse expr "an expression"
--            "a (b c)"
--            (appExpr () [varExpr () "a", appExpr () [varExpr () "b", varExpr () "c"]])
--
--        succeedParse expr "an expression"
--            "(\\xs => match xs with | (x :: xs) => x) [1,2,3]"
--            (appExpr () [lamExpr () [varPat () "xs"] (patExpr () [varExpr () "xs"] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")]), lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]])
--
--    describe "\nConstructors\n" $ do
--
--        succeedParse expr "an expression"
--            "Some x"
--            (conExpr () "Some" [varExpr () "x"])
--            
--        succeedParse expr "an expression"
--            "None"
--            (conExpr () "None" [])
--
--        succeedParse expr "an expression"
--            "A B C"
--            (conExpr () "A" [conExpr () "B" [], conExpr () "C" []])
--
--        succeedParse expr "an expression"
--            "A b c"
--            (conExpr () "A" [varExpr () "b", varExpr () "c"])
--
--        succeedParse expr "an exprssion"
--            "A (B C) D"
--            (conExpr () "A" [conExpr () "B" [conExpr () "C" []], conExpr () "D" []])
--
--    --  Mixed expressions
--
--    describe "\nMixed expressions\n" $ do
--
--        succeedParse expr "an expression"
--            "(fun | (x :: xs) => x) [1,2,3]"
--            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]])
--
--        succeedParse expr "an expression"
--            "(fun (x :: xs) => x) [1,2,3]"
--            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]])
--
--        succeedParse expr "an expression"
--            "(fun x :: xs => x) [1,2,3]"
--            (appExpr () [patExpr () [] [Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (varExpr () "x")], lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]])
--
--        succeedParse expr "an expression"
--            "fun [] => [] | y :: ys => f y :: mu ys"
--            (patExpr () [] [Clause [lstPat () []] [] (lstExpr () []), Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "y"], appExpr () [varExpr () "mu", varExpr () "ys"]])])
--
--        succeedParse expr "an expression"
--            "letfix mu = fun [] => [] | y :: ys => f y :: mu ys in mu xs"
--            (fixExpr () "mu" (patExpr () [] 
--                [ Clause [lstPat () []] [] (lstExpr () [])
--                , Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "y"], appExpr () [varExpr () "mu", varExpr () "ys"]])
--                ]) (appExpr () [varExpr () "mu", varExpr () "xs"]))
--
--        succeedParse expr "an expression"
--            "let map f xs = letfix mu = fun [] => [] | y :: ys => f y :: mu ys in mu xs in let xs = [1, 2, 3] in xs.map (\\x => x + 1)"
--            (letExpr () (BFun "map" [varPat () "f", varPat () "xs"]) (fixExpr () "mu" (patExpr () [] 
--                [ Clause [lstPat () []] [] (lstExpr () [])
--                , Clause [conPat () "(::)" [varPat () "y", varPat () "ys"]] [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "y"], appExpr () [varExpr () "mu", varExpr () "ys"]])
--                ]) (appExpr () [varExpr () "mu", varExpr () "xs"])) (letExpr () (BLet (varPat () "xs")) (lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]) (dotExpr () (varExpr () "xs") (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))]))))
--
--        succeedParse expr "an expression"
--            "letfix len = fun [] => 0 | x :: xs => 1 + len xs in [].len"
--            (fixExpr () "len" (patExpr () [] [Clause [lstPat () []] [] (litExpr () (TInt 0)), Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (op2Expr () (OAdd ()) (litExpr () (TInt 1)) (appExpr () [varExpr () "len", varExpr () "xs"]))]) (dotExpr () (lstExpr () []) (varExpr () "len")))
--
--        succeedParse expr "an expression"
--            "letfix len = fun [] => 0 | x :: xs => 1 + len xs in [1,2,3,4,5].len"
--            (fixExpr () "len" (patExpr () [] [Clause [lstPat () []] [] (litExpr () (TInt 0)), Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] [] (op2Expr () (OAdd ()) (litExpr () (TInt 1)) (appExpr () [varExpr () "len", varExpr () "xs"]))]) (dotExpr () (lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3), litExpr () (TInt 4), litExpr () (TInt 5)]) (varExpr () "len")))
--
--        succeedParse expr "an expression"
--            "let first (a, b) = a in (5, ()).first"
--            (letExpr () (BFun "first" [tupPat () [varPat () "a", varPat () "b"]]) (varExpr () "a") (dotExpr () (tupExpr () [litExpr () (TInt 5), litExpr () TUnit]) (varExpr () "first")))
--
----        succeedParse expr "an expression"
----            "f a b.length"
----            (appExpr () [varExpr () "f", varExpr () "a", dotExpr () (varExpr () "b") (varExpr () "length")])
----
----        succeedParse expr "an expression"
----            "f a.length b"
----            (appExpr () [varExpr () "f", dotExpr () (varExpr () "a") (varExpr () "length"), varExpr () "b"])
----
----        succeedParse expr "an expression"
----            "f a.length b c"
----            (appExpr () [varExpr () "f", dotExpr () (varExpr () "a") (varExpr () "length"), varExpr () "b", varExpr () "c"])
----
----        succeedParse expr "an expression"
----            "f xs.length.toString b c"
----            (appExpr () [varExpr () "f", dotExpr () (dotExpr () (varExpr () "xs") (varExpr () "length")) (varExpr () "toString"), varExpr () "b", varExpr () "c"])
--
--        succeedParse expr "an expression"
--            "withDefault 0 ([1,2,3].head)"
--            (appExpr () [varExpr () "withDefault", litExpr () (TInt 0), dotExpr () (lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]) (varExpr () "head")])
--
--        -- let withDefault(default) = fun 
--        --   | None       => default
--        --   | Some value => value 
--        -- in 
--        --   let head = fun 
--        --     | []     => None 
--        --     | x :: _ => Some x 
--        --   in 
--        --     withDefault 0 [1,2,3].head"
--
--        succeedParse expr "an expression"
--            "let withDefault default = fun None => default | Some value => value in let head = fun [] => None | x :: _ => Some x in withDefault 0 ([1,2,3].head)"
--            (letExpr () (BFun "withDefault" [varPat () "default"]) (patExpr () [] [Clause [conPat () "None" []] [] (varExpr () "default"), Clause [conPat () "Some" [varPat () "value"]] [] (varExpr () "value")])
--                (letExpr () (BLet (varPat () "head")) (patExpr () [] [Clause [lstPat () []] [] (conExpr () "None" []), Clause [conPat () "(::)" [varPat () "x", anyPat ()]] [] (conExpr () "Some" [varExpr () "x"])])
--                    (appExpr () [varExpr () "withDefault", litExpr () (TInt 0), dotExpr () (lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]) (varExpr () "head")])))
--
--        -- let withDefault(default) = \None => default | Some value => value 
--        -- in 
--        --   let head = fun 
--        --     | []     => None 
--        --     | x :: _ => Some x 
--        --   in 
--        --     withDefault 0 [1,2,3].head"
--
--        succeedParse expr "an expression"
--            "let withDefault default = \\None => default | Some value => value in let head = \\[] => None | x :: _ => Some x in withDefault 0 ([1,2,3].head)"
--            (letExpr () (BFun "withDefault" [varPat () "default"]) (patExpr () [] [Clause [conPat () "None" []] [] (varExpr () "default"), Clause [conPat () "Some" [varPat () "value"]] [] (varExpr () "value")])
--                (letExpr () (BLet (varPat () "head")) (patExpr () [] [Clause [lstPat () []] [] (conExpr () "None" []), Clause [conPat () "(::)" [varPat () "x", anyPat ()]] [] (conExpr () "Some" [varExpr () "x"])])
--                    (appExpr () [varExpr () "withDefault", litExpr () (TInt 0), dotExpr () (lstExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]) (varExpr () "head")])))
--
--    --  Operators
--
--    describe "\nOperators\n" $ do
--
--        succeedParse expr "an expression"
--            "x + y"
--            (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y"))
--
--        -- Addition associativity
--
--        succeedParse expr "an expression"
--            "x + y + z"
--            (op2Expr () (OAdd ()) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (varExpr () "z"))
--
--        -- Operator precedence
--
--        succeedParse expr "an expression"
--            "x * y + z"
--            (op2Expr () (OAdd ()) (op2Expr () (OMul ()) (varExpr () "x") (varExpr () "y")) (varExpr () "z"))
--
--        succeedParse expr "an expression"
--            "xs.length"
--            (dotExpr () (varExpr () "xs") (varExpr () "length"))
--
--        succeedParse expr "an expression"
--            "xs.length.toString"
--            (dotExpr () (dotExpr () (varExpr () "xs") (varExpr () "length")) (varExpr () "toString"))
--
--        succeedParse expr "an expression"
--            "xs.map (\\x => x + 1)"
--            (dotExpr () (varExpr () "xs") (appExpr () [varExpr () "map", lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))]))
--
--        succeedParse expr "an expression"
--            "x > y"
--            (op2Expr () (OGt ()) (varExpr () "x") (varExpr () "y")) 
--
--        failParse expr "an expression"
--            "(x > y > z)"
--
--
--    --  Top-level definitions
--
--    describe "\nTop-level definitions\n" $ do
--
--        succeedParse definition "a top-level definition"
--            "fn x y = x + y"
--            (Def "fn" [Clause [varPat () "x", varPat () "y"] [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y"))] [])
--
--        succeedParse definition "a top-level definition"
--            "fn x y = x + y\nfn _ _ = 100"
--            (Def "fn" 
--                [ Clause [varPat () "x", varPat () "y"] [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y"))
--                , Clause [anyPat (), anyPat ()] [] (litExpr () (TInt 100))
--                ] [])
--
--        succeedParse definition "a top-level definition"
--            "fn x y (Some z) = x + y\nfn _ _ _ = 100"
--            (Def "fn" 
--                [ Clause [varPat () "x", varPat () "y", conPat () "Some" [varPat () "z"]] [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y"))
--                , Clause [anyPat (), anyPat (), anyPat ()] [] (litExpr () (TInt 100))
--                ] [])
--
--        succeedParse definition "a top-level definition"
--            "number = 5"
--            (Def "number" [Clause [] [] (litExpr () (TInt 5))] [])
--
--        succeedParse definition "a top-level definition"
--            "fn x =\n  x + 1"
--            (Def "fn" [Clause [varPat () "x"] [] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))] [])
--
--        succeedParse definition "a top-level definition"
--            "fn x\n  = x + 1"
--            (Def "fn" [Clause [varPat () "x"] [] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))] [])
--
--        succeedParse definition "a top-level definition"
--            "fn x when x > 3 = 5"
--            (Def "fn" [Clause [varPat () "x"] [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 5))] [])
--
--        succeedParse definition "a top-level definition"
--            "fn x when x > 3 = 5\nfn _ = 6"
--            (Def "fn" 
--                [ Clause [varPat () "x"] [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 5))
--                , Clause [anyPat ()] [] (litExpr () (TInt 6))
--                ] [])
--
