{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Print
  ( module Data.Text.Prettyprint.Doc
  , prettyPrint
  ) where

import Control.Arrow ((>>>))
import Data.Functor.Foldable
import Data.List (intersperse)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Tau.Expr
import Tau.Type
import qualified Data.Text as Text

instance Pretty Expr where
    pretty = prettyExpr 0

prettyExpr :: Int -> Expr -> Doc a
prettyExpr n = unfix >>> \case
    VarS name ->
        pretty name

    LamS name body ->
        wrap n (backslash <> pretty name <+> "=>" <+> pretty body)

    AppS [expr] ->
        prettyExpr n expr

    AppS exprs ->
        wrap n (hsep (prettyExpr (succ n) <$> exprs))

    LitS prim ->
        pretty prim

    LetS name expr body ->
        wrap n ("let" <+> pretty name <+> equals <+> pretty expr <+> "in" <+> pretty body)

    RecS name expr body ->
        wrap n ("let rec" <+> pretty name <+> equals <+> pretty expr <+> "in" <+> pretty body)

    IfS cond true false ->
        wrap n ("if" <+> pretty cond <+> "then" <+> pretty true <+> "else" <+> pretty false)

    MatchS expr clss ->
        wrap n ("match" <+> pretty expr <+> "with" <+> hsep (matchClause <$> clss))

    LamMatchS clss ->
        wrap n (backslash <> "match" <+> hsep (matchClause <$> clss))

    OpS ops ->
        wrap n (prettyOp 0 ops)

    AnnS expr ty ->
        wrap n (pretty expr <+> colon <+> pretty ty)

    ErrS ->
        "<<error>>"

wrap :: Int -> Doc a -> Doc a
wrap 0 doc = doc
wrap _ doc = parens doc

matchClause :: (Pattern, Expr) -> Doc a
matchClause (pat, expr) = pipe <+> pretty pat <+> "=>" <+> pretty expr

prettyOp :: Int -> Op -> Doc a
prettyOp n = \case
    EqS a b  -> pretty a <+> "==" <+> pretty b
    AddS a b -> hsep (intersperse "+" (next <$> flattenOp AddOp [a, b]))
    MulS a b -> hsep (intersperse "*" (next <$> flattenOp MulOp [a, b]))
    AndS a b -> hsep (intersperse "&&" (next <$> flattenOp AndOp [a, b]))
    OrS a b  -> hsep (intersperse "||" (next <$> flattenOp OrOp [a, b]))
    SubS a b -> next a <+> "-" <+> next b
    LtS a b  -> next a <+> "<" <+> next b
    GtS a b  -> next a <+> ">" <+> next b
    NegS a   -> "-" <> next a
    NotS a   -> "not" <+> next a
  where
    next = prettyExpr (succ n)

data OpType = AddOp | MulOp | AndOp | OrOp deriving (Eq, Show)

flattenOp :: OpType -> [Fix ExprF] -> [Expr]
flattenOp _ [] = []
flattenOp op (x:xs) =
    case unfix x of
        OpS (AddS a b) | AddOp == op -> flattenOp op [a, b] <> rest
        OpS (MulS a b) | MulOp == op -> flattenOp op [a, b] <> rest
        OpS (AndS a b) | AndOp == op -> flattenOp op [a, b] <> rest
        OpS (OrS a b)  | OrOp  == op -> flattenOp op [a, b] <> rest
        _ -> x:rest
  where
    rest = flattenOp op xs

instance Pretty Prim where
    pretty = \case
        Unit      -> "()"
        Bool b    -> pretty b
        Int n     -> pretty n
        Integer n -> pretty n
        Float f   -> pretty f
        Char c    -> pretty c
        String s  -> pretty s

instance Pretty Pattern where
    pretty = unfix >>> \case
        ConP name ps@(_:_) -> pretty name <+> hsep (prettyPattern . unfix <$> ps)
        pat                -> prettyPattern pat

prettyPattern :: PatternF (Fix PatternF) -> Doc a
prettyPattern = \case
    VarP name    -> pretty name
    LitP prim    -> pretty prim
    ConP name [] -> pretty name
    con@ConP{}   -> parens $ pretty (Fix con)
    AnyP         -> "_"

instance Pretty Type where
    pretty = cata $ \case
        ConT name -> pretty name
        VarT name -> pretty name
        ArrT a b  -> a <+> "->" <+> b
        AppT a b  -> a <+> b

instance Pretty Kind where
    pretty = cata $ \case
        VarK name  -> pretty name
        ArrK a b   -> a <+> "->" <+> b
        StarK      -> "*"

instance Pretty TyClass where
    pretty (TyCl name ty) = pretty name <+> pretty ty

instance Pretty Scheme where
    pretty (Forall vars clcs ty) = forall <> classes <> pretty ty where
        forall
          | null vars = mempty
          | otherwise = "forall" <+> pretty (Text.unwords vars) <> dot <> space
        classes
          | null clcs = mempty
          | otherwise = tupled (pretty <$> clcs) <+> "=>" <> space

--instance Pretty (Value m) where
--    pretty (Data name args) = pretty name <+> hsep (prettyArg <$> args)
--    pretty value = prettyArg value
--
--prettyArg (Value prim)   = pretty prim
--prettyArg (Data name []) = pretty name
--prettyArg dat@Data{}     = parens (pretty dat)
--prettyArg Closure{}      = "<<function>>"

prettyPrint :: (Pretty p) => p -> Text
prettyPrint = renderStrict . layoutPretty defaultLayoutOptions . pretty
