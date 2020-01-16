{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Core.Parser where

import Control.Monad.Combinators.Expr
import Data.Functor (($>))
import Data.Text (Text, pack)
import Data.Void
import Tau.Core (Expr)
import Tau.Util
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Text as Text
import qualified Tau.Core as Core
import qualified Text.Megaparsec.Char.Lexer as Lex


type Parser = Parsec Void Text


data Ast
    = Var !Name
    | App !Ast !Ast
    | If  !Ast !Ast !Ast
    | Let !Name !Ast !Ast
    | Lambda !Name !Ast
    | Op1 !Op1 !Ast
    | Op2 !Op2 !Ast !Ast
    | Int !Integer
    | Bool !Bool
    | String !Text
    | Char !Char
    | Unit
    deriving (Show, Eq)


data Op1
    = Neg
    deriving (Show, Eq)


data Op2
    = Add
    | Sub
    | Mul
    | Eq
    deriving (Show, Eq)


spaces :: Parser ()
spaces = Lex.space
    space1
    (Lex.skipLineComment "--")
    (Lex.skipBlockComment "{-" "-}")


-- | Parse a single lexeme. By convention, whitespace is consumed after lexemes.
--
lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme spaces


symbol :: Text -> Parser Text
symbol = Lex.symbol spaces


-- | Parse something surrounded by a pair of parentheses.
--
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


-- | Parse a positive integer.
--
integer :: Parser Integer
integer = lexeme Lex.decimal


keyword :: Text -> Parser ()
keyword token =
    string token *> notFollowedBy alphaNumChar *> spaces


reserved :: List String
reserved =
    [ "let"
    , "in"
    , "if"
    , "then"
    , "else"
    , "True"
    , "False"
    ]


identifier :: Parser Text
identifier = lexeme $ try $ do
    head <- letterChar
    tail <- many alphaNumChar
    let name = head : tail
    if name `elem` reserved then
        fail "Reserved word"

    else
        pure (pack name)


ifClause :: Parser Ast
ifClause = do
    keyword "if"
    cond <- expr
    keyword "then"
    true <- expr
    keyword "else"
    false <- expr
    pure (If cond true false)


letBinding :: Parser Ast
letBinding = do
    keyword "let"
    var <- identifier
    symbol "="
    exp <- expr
    keyword "in"
    body <- expr
    pure (Let var exp body)


variable :: Parser Ast
variable = Var <$> identifier


lambda :: Parser Ast
lambda = do
    symbol "\\"
    var <- identifier
    symbol "->"
    body <- expr
    pure (Lambda var body)


int :: Parser Ast
int = Int <$> integer


bool :: Parser Ast
bool = true <|> false where
    true = keyword "True" $> Bool True
    false = keyword "False" $> Bool False


unit :: Parser Ast
unit = symbol "()" $> Unit


ch :: Parser Ast
ch = do
    chr <- char '\'' *> Lex.charLiteral <* char '\''
    pure (Char chr)


str :: Parser Ast
str = do
    str <- char '"' *> manyTill Lex.charLiteral (char '"')
    pure $ String $ Text.pack str


term :: Parser Ast
term = do
    ast <- some asts
    pure (foldl1 App ast)
  where
    asts = unit
        <|> parens expr
        <|> ifClause
        <|> letBinding
        <|> lambda
        <|> int
        <|> bool
        <|> lexeme ch
        <|> lexeme str
        <|> variable


prefix :: Text -> (a -> a) -> Operator Parser a
prefix name f = Prefix (f <$ symbol name)


postfix :: Text -> (a -> a) -> Operator Parser a
postfix name f = Postfix (f <$ symbol name)


operator :: List (List (Operator Parser Ast))
operator =
    [ [ prefix "-" (Op1 Neg)
      ]
    , [ InfixL (Op2 Mul <$ symbol "*")
      ]
    , [ InfixL (Op2 Add <$ symbol "+")
      , InfixL (Op2 Sub <$ symbol "-")
      ]
    , [ InfixN (Op2 Eq <$ symbol "==")
    ] ]


expr :: Parser Ast
expr = makeExprParser term operator


ast :: Parser Ast
ast = spaces *> expr <* eof


toExpr :: Ast -> Expr
toExpr = \case

    Var name ->
       Core.Var name

    App fun arg ->
       Core.App (toExpr fun) (toExpr arg)

    If cond true false ->
       Core.If (toExpr cond) (toExpr true) (toExpr false)

    Let name exp body ->
       Core.Let name (toExpr exp) (toExpr body)

    Lambda name body ->
       Core.Lam name (toExpr body)

    Op1 Neg a ->
       Core.Neg (toExpr a)

    Op2 op2 a b ->
       Core.Op (toOp2 op2) (toExpr a) (toExpr b)

    Int n ->
       Core.Lit (Core.Int n)

    Bool b ->
       Core.Lit (Core.Bool b)

    String str ->
        Core.Lit (Core.String str)

    Char ch ->
        Core.Lit (Core.Char ch)

    Unit ->
        Core.Lit Core.Unit


toOp2 :: Op2 -> Core.Op
toOp2 = \case

    Add ->
        Core.Add

    Sub ->
        Core.Sub

    Mul ->
        Core.Mul

    Eq ->
        Core.Eq
