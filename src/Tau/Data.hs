{-# LANGUAGE OverloadedStrings #-}
module Tau.Data where

import Data.Text.Prettyprint.Doc
import Tau.Util
import Tau.Type

-- | Product type
data Product = Prod Name [Type]
    deriving (Show, Eq)

-- | Sum type
data Data = Sum Type [Product]
    deriving (Show, Eq)

instance Pretty Data where
    pretty (Sum ty prods) = 
        "type" <+> pretty ty <+> "=" 
               <+> hsep (punctuate "|" (pretty <$> prods))

instance Pretty Product where
    pretty (Prod con types) = pretty con <+> hsep (pretty <$> types)
