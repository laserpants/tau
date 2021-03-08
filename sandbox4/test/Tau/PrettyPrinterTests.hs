{-# LANGUAGE OverloadedStrings #-}
module Tau.PrettyPrinterTests where

import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc
import Tau.Lang.Expr
import Tau.Lang.Pretty
import Tau.Lang.Type
import Tau.Util
import Test.Hspec
import Utils
import qualified Data.Text as Text

prettyPrintsTo :: (Pretty p) => p -> Text -> SpecWith ()
prettyPrintsTo input expect = 
    describe (unpack (prettyPrint input)) $ do

        it ("✔ matches " <> unpack expect) $
            prettyPrint input == expect

testPrettyPrinter :: SpecWith ()
testPrettyPrinter = do

    -- Types

    prettyPrintsTo
        (tInt :: Type)
        "Int"

    prettyPrintsTo
        (tApp (tCon (kArr kTyp kTyp) "List") tInt :: Type)
        "List Int"

    prettyPrintsTo
        (tApp (tCon (kArr kTyp kTyp) "List") tInt `tArr` tVar kTyp "a" :: Type)
        "List Int -> a"

    -- Tuples

    prettyPrintsTo
        (tupExpr () [varExpr () "x", litExpr () (LInt 5)] :: Expr () (Pattern ()) [Pattern ()] r (Op1 ()) (Op2 ()))
        "(x, 5)"

