{-# LANGUAGE OverloadedStrings #-}
module Tau.PrettyTests where

import Data.Text.Prettyprint.Doc
import Tau.Lang
import Tau.Pretty
import Tau.Row
import Tau.Type
import Tau.Tool
import Test.Hspec hiding (describe, it)
import Utils
import qualified Data.Text as Text

suceedPrint :: (Pretty p) => p -> String -> SpecWith ()
suceedPrint p str =
    describe (Text.pack output) $ it "✔ OK" $ output == str where
    output = show (pretty p)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testPrettyPrim :: SpecWith ()
testPrettyPrim = do

    suceedPrint
        TUnit
        "()"

    suceedPrint
        (TString "klingon") 
        "\"klingon\""

    suceedPrint
        (TChar 'a') 
        "'a'"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

suceedPrintType :: Type -> String -> SpecWith ()
suceedPrintType = suceedPrint

testPrettyType :: SpecWith ()
testPrettyType = do

    suceedPrintType 
        (_a `tArr` _b) 
        "a -> b"

    suceedPrintType 
        tInt
        "Int"

    suceedPrintType 
        (_a `tArr` _b `tArr` _c) 
        "a -> b -> c"

    suceedPrintType 
        ((_a `tArr` _b) `tArr` _c) 
        "(a -> b) -> c"

    suceedPrintType 
        (tList tInt `tArr` _b `tArr` _c) 
        "List Int -> b -> c"

    suceedPrintType 
        (tList (tList tInt)) 
        "List (List Int)"

    suceedPrintType 
        (tList (tInt `tArr` _a)) 
        "List (Int -> a)"

    suceedPrintType 
        (tApp kTyp (tApp kFun (tCon kFun2 "C") tInt) tInt) 
        "C Int Int"

    suceedPrintType 
        (tApp kTyp (tApp kFun (tCon kFun2 "C") tInt) tInt `tArr` _a) 
        "C Int Int -> a"

    suceedPrintType 
        (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) tInt `tArr` _a) 
        "C (a -> a) Int -> a"

    suceedPrintType 
        (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) (_b `tArr` _b) `tArr` _a) 
        "C (a -> a) (b -> b) -> a"

    suceedPrintType 
        (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) (tApp kTyp (tCon kFun "D") _b) `tArr` _a) 
        "C (a -> a) (D b) -> a"

--    suceedPrintType 
--        (tApp kTyp (tCon kTyp (kArr kRow kTyp) "#Record") (tApp kTyp (tApp kTyp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") (tVar kTyp "b")) (tVar kRow "r"))))
--        "{ id : a, name : b | r }"

--    suceedPrintType 
--        (tApp (tCon (kArr kRow kTyp) "#Record") (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{id}") (tVar kTyp "a")) (tApp (tApp (tCon (kArr kTyp (kArr kRow kRow)) "{name}") (tVar kTyp "b")) (tCon kRow "{}"))))
--        "{ id : a, name : b }"

    suceedPrintType
        (tApp kTyp (tApp kTyp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tCon kTyp "String")) (tCon kTyp "Bool"))
        "(String, Bool)"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testPrettyKind :: SpecWith ()
testPrettyKind = do

    suceedPrint
        kRow
        "Row"

    suceedPrint
        (kTyp `kArr` kTyp) 
        "* -> *"

    suceedPrint
        (kTyp `kArr` kTyp `kArr` kTyp) 
        "* -> * -> *"

    suceedPrint
        ((kTyp `kArr` kTyp) `kArr` kTyp) 
        "(* -> *) -> *"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

suceedPrintPattern :: ProgPattern t -> String -> SpecWith ()
suceedPrintPattern = suceedPrint

testPrettyPattern :: SpecWith ()
testPrettyPattern = do

    suceedPrintPattern
        (varPat () "v")
        "v"

    suceedPrintPattern
        (anyPat ())
        "_"

    suceedPrintPattern
        (litPat () (TInt 5))
        "5"

    suceedPrintPattern
        (orPat () (varPat () "v") (litPat () (TInt 5)))
        "v or 5"

    suceedPrintPattern
        (asPat () "five" (litPat () (TInt 5)))
        "5 as five"

    suceedPrintPattern
        (tuplePat () [varPat () "x", varPat () "y"])
        "(x, y)"

    suceedPrintPattern
        (tuplePat () [varPat () "x", anyPat ()])
        "(x, _)"

    suceedPrintPattern
        (listPat () [varPat () "x", anyPat ()])
        "[x, _]"

    suceedPrintPattern
        (listPat () [])
        "[]"

    suceedPrintPattern
        (litPat () TUnit)
        "()"

--    suceedPrintPattern
--        (recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)))
--        "{ id = id, name = name }"
--
--    suceedPrintPattern
--        (recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") rNil)))
--        "{ id = id, name = name }"
--
--    suceedPrintPattern
--        (recordPat () (rExt "name" (anyPat ()) (rExt "id" (varPat () "id") rNil)))
--        "{ id = id, name = _ }"
--
--    suceedPrintPattern
--        (recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") (rVar (varPat () "r")))))
--        "{ id = id, name = name | r }"

    describe "Constructor patterns" $ do

        suceedPrintPattern
            (conPat () "C" [])
            "C"

        suceedPrintPattern
            (conPat () "C" [varPat () "x", varPat () "y"])
            "C x y"

        suceedPrintPattern
            (conPat () "C" [varPat () "x", conPat () "D" [varPat () "y", varPat () "z"]])
            "C x (D y z)"

        suceedPrintPattern
            (conPat () "C" [varPat () "x", conPat () "D" []])
            "C x D"

        suceedPrintPattern
            (conPat () "C" [orPat () (varPat () "x") (varPat () "y")])
            "C (x or y)"

        suceedPrintPattern
            (conPat () "C" [varPat () "x", asPat () "d" (conPat () "D" [varPat () "y"])])
            "C x (D y as d)"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testPrettyPredicates :: SpecWith ()
testPrettyPredicates = do

    suceedPrint
        (InClass "Show" _a)
        "Show a"

    suceedPrint
        (InClass "Eq" tInt :: Predicate)
        "Eq Int"
