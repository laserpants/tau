{-# LANGUAGE OverloadedStrings #-}
module Tau.PrettyTests where

import Data.Text.Prettyprint.Doc
import Tau.Pretty
import Tau.Type
import Test.Hspec hiding (describe, it)
import Utils
import qualified Data.Text as Text

suceedPrint :: (Pretty p) => p -> String -> SpecWith ()
suceedPrint p str =
    describe (Text.pack output) $ it "✔ OK" $ output == str where
    output = show (pretty p)

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
        (tApp (tApp (tCon kFun2 "C") tInt) tInt) 
        "C Int Int"

    suceedPrintType 
        (tApp (tApp (tCon kFun2 "C") tInt) tInt `tArr` _a) 
        "C Int Int -> a"

    suceedPrintType 
        (tApp (tApp (tCon kFun2 "C") (_a `tArr` _a)) tInt `tArr` _a) 
        "C (a -> a) Int -> a"

    suceedPrintType 
        (tApp (tApp (tCon kFun2 "C") (_a `tArr` _a)) (_b `tArr` _b) `tArr` _a) 
        "C (a -> a) (b -> b) -> a"

    suceedPrintType 
        (tApp (tApp (tCon kFun2 "C") (_a `tArr` _a)) (tApp (tCon kFun "D") _b) `tArr` _a) 
        "C (a -> a) (D b) -> a"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

testPrettyKind :: SpecWith ()
testPrettyKind = do

    suceedPrint
        kRow
        "r"

    suceedPrint
        (kTyp `kArr` kTyp) 
        "* -> *"

    suceedPrint
        (kTyp `kArr` kTyp `kArr` kTyp) 
        "* -> * -> *"

    suceedPrint
        ((kTyp `kArr` kTyp) `kArr` kTyp) 
        "(* -> *) -> *"
