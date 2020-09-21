{-# LANGUAGE OverloadedStrings #-}
module Tau.Data where

import Data.Text.Prettyprint.Doc
import Tau.Util
import Tau.Type

-- | Product type
data Product = Prod Name [Type]
    deriving (Show, Eq)

-- | Sum type
data Data = Sum Name [Name] [Product]
    deriving (Show, Eq)

instance Pretty Data where
    pretty (Sum con vars prods) =
        case prods of
            []   -> hsep (tcon mempty)
            [p]  -> hsep (tcon (dcon equals p))
            p:ps -> vsep [nest 2 (vsep (tcon (dcon equals p) <> (dcon pipe <$> ps)))]
      where
        tcon rest = ["type" <+> pretty con <> prettyVars, rest]
        dcon sym prod = sym <+> pretty prod
        prettyVars
            | null vars = mempty
            | otherwise = hsep (pretty <$> vars)

instance Pretty Product where
    pretty (Prod con [])    = pretty con
    pretty (Prod con types) = pretty con <+> hsep (prettyType <$> types)

prettyType :: Type -> Doc a
prettyType ty =
    case unfix ty of
        VarT t    -> pretty t
        ConT name -> pretty name
        _         -> parens (pretty ty)
