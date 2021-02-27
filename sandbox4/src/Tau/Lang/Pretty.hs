{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Pretty where

import Data.Text.Prettyprint.Doc
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util

instance Pretty Literal where
    pretty = \case
        LUnit      -> parens mempty
        LBool b    -> pretty b
        LInt n     -> pretty n
        LInteger n -> pretty n
        LFloat f   -> pretty f
        LChar c    -> squotes (pretty c)
        LString s  -> dquotes (pretty s)

instance Pretty Type where
    pretty = para $ \case
        TApp a b ->
            undefined

        TArr a b -> 
            undefined

        TCon _ name -> pretty name

        TVar _ name -> pretty name

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var    -> pretty var
        PCon t con ps -> undefined
        PLit _ lit    -> pretty lit
        PRec _ fields -> prettyRecord equals (snd <$> fields)
        PAs  _ name p -> pretty (fst p) <+> "as" <+> pretty name
        POr  _ p1 p2  -> pretty (fst p1) <+> "or" <+> pretty (fst p2)
        PAny _        -> "_"

instance Pretty (Expr t p q r) where
    pretty = para $ \case
        _ ->
            undefined

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

--prettyRecord :: Doc a -> FieldSet t (Doc a) -> Doc a
prettyRecord sep fset
    | null fields = braces ""
    | otherwise   = lbrace <+> commaSep (prettyField <$> fields) <+> rbrace
  where
    fields = fieldList fset
    prettyField (_, key, val) = pretty key <+> sep <+> val

