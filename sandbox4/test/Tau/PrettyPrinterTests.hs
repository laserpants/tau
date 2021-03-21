{-# LANGUAGE OverloadedStrings #-}
module Tau.PrettyPrinterTests where

import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc
import Tau.Lang.Expr
import Tau.Lang.Pretty
import Tau.Lang.Prog
import Tau.Lang.Type
import Tau.Util
import Test.Hspec
import Utils
import qualified Data.Text as Text

prettyPrintsTo :: (Pretty p) => p -> Text -> SpecWith ()
prettyPrintsTo input expect = 
    describe (unpack (prettyPrint input)) $ do

        it ("✔ matches the expected output " <> unpack expect) $
            prettyPrint input == expect

testPrettyPrinter :: SpecWith ()
testPrettyPrinter = do

    -- Types

    describe "\nTypes\n" $ do

        prettyPrintsTo
            (tInt :: Type)
            "Int"

        prettyPrintsTo
            (tApp (tCon (kArr kTyp kTyp) "List") tInt :: Type)
            "List Int"

        prettyPrintsTo
            (tApp (tCon (kArr kTyp kTyp) "List") tInt `tArr` tVar kTyp "a" :: Type)
            "List Int -> a"
            
        prettyPrintsTo
            (tApp (tVar (kArr kTyp kTyp) "m") (tApp (tVar (kArr kTyp kTyp) "m") (tVar kTyp "a")) :: Type)
            "m (m a)"

        prettyPrintsTo
            ((tApp (tCon (kArr kTyp kTyp) "List") (tApp (tCon (kArr kTyp kTyp) "List") tInt) `tArr` tVar kTyp "a") :: Type)
            "List (List Int) -> a"

        prettyPrintsTo
            ((tApp (tCon (kArr kTyp kTyp) "List") (tApp (tCon (kArr kTyp kTyp) "List") tInt) `tArr` tVar kTyp "a" `tArr` tVar kTyp "b") :: Type)
            "List (List Int) -> a -> b"

        prettyPrintsTo
            (tVar kTyp "a" `tArr` tApp (tCon (kArr kTyp kTyp) "List") (tApp (tCon (kArr kTyp kTyp) "List") tInt) :: Type)
            "a -> List (List Int)"

        prettyPrintsTo
            (tApp (tApp (tCon (kArr kTyp kTyp) "(,)") tInt) tInt :: Type)
            "(Int, Int)"

        prettyPrintsTo
            (((tApp (tApp (tCon (kArr kTyp kTyp) "(,)") tInt) tInt :: Type) `tArr` tVar kTyp "a") :: Type)
            "(Int, Int) -> a"

    -- Tuples

    describe "\nTuples\n" $ do

        prettyPrintsTo
            (tupExpr () [varExpr () "x", litExpr () (TInt 5)] :: ProgExpr)
            "(x, 5)"

    -- Pattern clauses
