{-# LANGUAGE StrictData #-}
module Tau.Util 
  ( module Data.Functor.Foldable
  , Name
  , Algebra
  , nameSupply
  , prettyPrint
  ) where

import Data.Functor.Foldable
import Data.Text (Text)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import qualified Data.Text.Lazy as Text (toStrict)

type Name = Text

nameSupply :: Text -> [Name]
nameSupply prefix = (prefix <>) . pack <$> nats
  where
    nats = [1..] :: [Integer]
    pack = Text.toStrict . toLazyText . decimal

type Algebra f a = f a -> a

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
