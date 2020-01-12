{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Core.Parser where

import Control.Monad.Combinators.Expr
import Data.Text (Text, pack)
import Data.Void
import Tau.Core (Expr)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lex
import qualified Tau.Core as Core


type Parser = Parsec Void Text


type Name = Text


data Ast 
    = Var Name
    | App Ast Ast
    | If Ast Ast Ast
    | Let Name Ast Ast
    | Lambda Name Ast
    | Op2 Op2 Ast Ast
    | Bool Bool
    | Int Integer
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


-- | By convention, whitespace is consumed after lexemes.
--
lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme spaces


symbol :: Text -> Parser Text
symbol = Lex.symbol spaces


-- | Parse something between a pair of parentheses.
--
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")


-- | Parse an integer.
--
integer :: Parser Integer
integer = lexeme Lex.decimal


keyword :: Text -> Parser ()
keyword token = 
    string token *> notFollowedBy alphaNumChar *> spaces


reserved :: [String]
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


---


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


bool :: Parser Ast
bool = true <|> false
  where
    true = keyword "True" *> pure (Bool True)
    false = keyword "False" *> pure (Bool False)


int :: Parser Ast
int = do
    num <- integer
    pure (Int num)


term :: Parser Ast
term = do
    exps <- some ast
    pure (foldl1 App exps)
  where
    ast = do 
        parens expr
            <|> ifClause
            <|> letBinding
            <|> lambda
            <|> bool
            <|> int
            <|> variable


binary :: Text -> (a -> a -> a) -> Operator Parser a
binary name f = InfixL (f <$ symbol name)


prefix :: Text -> (a -> a) -> Operator Parser a
prefix name f = Prefix (f <$ symbol name)


postfix :: Text -> (a -> a) -> Operator Parser a
postfix name f = Postfix (f <$ symbol name)


operator :: [[Operator Parser Ast]]
operator =
    [ [ binary "+" (Op2 Add)
      , binary "-" (Op2 Sub)
      , binary "*" (Op2 Mul)
      , binary "==" (Op2 Eq)
    ] ]


expr :: Parser Ast
expr = makeExprParser term operator


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

    Op2 op2 a b ->
       Core.Op (toOp op2) (toExpr a) (toExpr b)

    Bool b ->
       Core.Lit (Core.Bool b)

    Int n ->
       Core.Lit (Core.Int n)


toOp :: Op2 -> Core.Op
toOp = \case

    Add ->
        Core.Add

    Sub ->
        Core.Sub

    Mul ->
        Core.Mul

    Eq ->
        Core.Eq
