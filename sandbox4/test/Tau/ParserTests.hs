{-# LANGUAGE OverloadedStrings #-}
module Tau.ParserTests where

import Data.Either
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Lang.Expr
import Tau.Lang.Parser
import Tau.Lang.Pretty
import Test.Hspec
import Text.Megaparsec hiding (ParseError)
import Utils

succeedParse :: (Eq p, Pretty p) => Parser p -> Text -> p -> SpecWith ()
succeedParse parser input expect = 
    describe (unpack input) $ do
        let result = parseWith parser input

        it "✔ succeeds to parse" $
            isRight result

        it ("✔ and gives the expected result: " <> prettyString expect) $
            Right expect == result

failParse :: Parser p -> Text -> SpecWith ()
failParse parser input = 
    describe (unpack input) $ do
        let result = parseWith parser input

        it "✗ fails to parse" $
            isLeft result

parseWith :: Parser p -> Text -> Either ParseError p
parseWith parser = runParser parser ""

testParser :: SpecWith ()
testParser = do

    succeedParse constructor_ 
        "Hello" 
        "Hello"

    failParse constructor_ 
        "hello"
    
