{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Parse where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Supply
import Control.Monad.Trans (lift)
import Data.Foldable (foldlM)
import Data.Function ((&))
import Data.Functor (($>))
import Data.Maybe (fromMaybe, fromJust)
import Data.Text (Text, pack, unpack, strip)
import Data.Void
import Tau.Misc
import Tau.Util hiding (parens, brackets, braces, commaSep)
import Text.Megaparsec
import Text.Megaparsec.Char
import TextShow
import qualified Text.Megaparsec.Char as Megaparsec
import qualified Text.Megaparsec.Char.Lexer as Lexer

type Parser = ParsecT Void Text (Supply Int)

runParserStack
  :: ParsecT Void Text (Supply Int) a
  -> String
  -> Text
  -> Either (ParseErrorBundle Text Void) a
runParserStack p s t = runSupplyNats (runParserT p s (strip t))

-------------------------------------------------------------------------------

spaces :: Parser ()
spaces = Lexer.space
    space1
    (Lexer.skipLineComment "--")
    (Lexer.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaces

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaces

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

surroundedBy :: Parser Text -> Parser a -> Parser a
surroundedBy parser = between parser parser

validChar :: Parser Char
validChar = alphaNumChar <|> char '_'

withInitial :: Parser Char -> Parser Text
withInitial parser = pack <$> ((:) <$> parser <*> many validChar)

keyword :: Text -> Parser ()
keyword tok = Megaparsec.string tok
    *> notFollowedBy alphaNumChar
    *> spaces

reserved :: [Text]
reserved =
    [ "and"
    , "as"
    , "else"
    , "fun"
    , "if"
    , "in"
    , "let"
    , "match"
    , "or"
    , "otherwise"
    , "then"
    , "where"
    , "when"
    , "with"
    ]

word :: Parser Text -> Parser Text
word parser = lexeme $ try $ do
    var <- parser
    if var `elem` reserved
        then fail ("Reserved word " <> unpack var)
        else pure var

-------------------------------------------------------------------------------

nameParser :: Parser Text
nameParser = word (withInitial (lowerChar <|> char '_'))

constructorParser :: Parser Name
constructorParser = word (withInitial upperChar)

commaSep :: Parser a -> Parser [a]
commaSep parser = parser `sepBy1` symbol ","

elements :: Parser a -> Parser [a]
elements = brackets . commaSep

components :: Parser a -> Parser [a]
components = parens . commaSep

fields :: Name -> Parser a -> Parser [(Name, a)]
fields stor parser = commaSep $ (,) <$> nameParser <*> (symbol stor *> parser)

rowParser
  :: Text
  -> Parser a
  -> (Name -> a -> a -> a)
  -> (Name -> a)
  -> a
  -> Parser a
rowParser stor parser rowCon varCon empty = braces $ do
    pairs <- fields stor parser
    rest <- optional (symbol "|" *> nameParser)
    pure $ case pairs of
        [] -> empty
        (label, value):row -> do
            let next = maybe empty varCon rest
            foldr (uncurry rowCon) (rowCon label value next) row

-------------------------------------------------------------------------------

primParser :: Parser Prim
primParser = parseUnit
    <|> parseTrue
    <|> parseFalse
    <|> parseChar
    <|> parseString
    <|> try parseFloat
    <|> parseIntegral
  where
    parseUnit      = symbol "()" $> TUnit
    parseTrue      = keyword "True"  $> TBool True
    parseFalse     = keyword "False" $> TBool False
    parseChar      = TChar <$> surroundedBy (symbol "'") printChar
    parseString    = lexeme (TString . pack <$> chars)
    parseFloat     = TDouble <$> lexeme Lexer.float
    parseIntegral  = TInteger <$> lexeme Lexer.decimal
    chars          = char '\"' *> manyTill Lexer.charLiteral (char '\"')

-------------------------------------------------------------------------------

kindVar :: Parser Kind
kindVar = lift (kVar . ("k" <>) . showt <$> supply)

typeParser :: Parser Type
typeParser = makeExprParser (try (parens typeParser) <|> parser)
    [[ InfixR (tArr <$ symbol "->") ]]
  where
    parser = do
        (t:ts) <- some typeFragmentParser
        foldlM (\s t -> kindVar >>= \k -> pure (tApp k s t)) t ts

typeFragmentParser :: Parser Type
typeFragmentParser = tVar <$> kindVar <*> nameParser
    <|> builtIn
    <|> tCon <$> kindVar <*> constructorParser
    <|> tTuple <$> components typeParser
    <|> recordTypeParser
  where
    recordTypeParser :: Parser Type
    recordTypeParser =
        symbol "{}" $> tRecord tRowNil
            <|> tRecord <$> rowParser ":" typeParser tRow (tVar kRow) tRowNil

    builtIn :: Parser Type
    builtIn = builtInType "Integer" kTyp
          <|> builtInType "Int"     kTyp
          <|> builtInType "Unit"    kTyp
          <|> builtInType "Bool"    kTyp
          <|> builtInType "Float"   kTyp
          <|> builtInType "Double"  kTyp
          <|> builtInType "Char"    kTyp
          <|> builtInType "String"  kTyp
          <|> builtInType "Nat"     kTyp
          <|> builtInType "List"    kFun
          <|> builtInType "Option"  kFun

    builtInType :: Name -> Kind -> Parser Type
    builtInType name kind = keyword name $> tCon kind name

