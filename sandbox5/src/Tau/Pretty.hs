{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where

import Control.Arrow ((<<<), (>>>))
import Data.Function ((&))
import Data.List (null, intersperse)
import Data.Text.Prettyprint.Doc
import Tau.Lang
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Prim where
    pretty = \case
        TUnit      -> "()"
        TBool b    -> pretty b
        TInt n     -> pretty n
        TInteger n -> pretty n
        TFloat f   -> pretty f
        TDouble d  -> pretty d
        TChar c    -> squotes (pretty c)
        TString s  -> dquotes (pretty s)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--instance (Eq e, Pretty e) => Pretty (Row e) where
--    pretty = prettyRow ":"

instance (Eq e, Pretty e) => Pretty (Row e) where
    pretty row = lbrace <+> prettyRow ":" (pretty <$> row) <+> rbrace

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (ProgPattern t) where
    pretty = para $ \case

        PCon _ con [] -> pretty con 
        PCon _ con ps -> pretty con <+> foldr pCon "" ps

        expr -> snd <$> expr & \case
            PVar    _ var    -> pretty var
            PLit    _ prim   -> pretty prim
            PAs     _ name p -> p <+> "as" <+> pretty name
            POr     _ p q    -> p <+> "or" <+> q
            PAny    _        -> "_"
            PTuple  _ ps     -> prettyTuple ps
            PList   _ ps     -> prettyList_ ps
            PRecord2 _ row    -> lbrace <+> prettyRow "=" row <+> rbrace

pCon :: (ProgPattern t, Doc a) -> Doc a -> Doc a
pCon (p1, doc1) doc2 =
    parensIf useLeft doc1 <> if "" == show doc2 then doc2 else " " <> doc2
  where
    useLeft = case project p1 of
        PCon _ _ ps | not (null ps) -> True
        PAs{}                       -> True
        POr{}                       -> True
        _                           -> False

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Kind where
    pretty = para $ \case
        KArr (k1, doc1) (_, doc2) -> parensIf useLeft doc1 <+> "->" <+> doc2
          where
            useLeft = 
                case project k1 of
                    KArr{} -> True
                    _      -> False

        KTyp   -> "*"    -- Value type
        KClass -> "!"    -- Type class constraint
        KRow   -> "row"  -- Row type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Type where
    pretty = para $ \case
        TArr (t1, doc1) (_, doc2) -> parensIf useLeft doc1 <+> "->" <+> doc2
          where
            useLeft = 
                case project t1 of
                    TArr{} -> True
                    _      -> False

        TApp (_, doc1) (t2, doc2) -> doc1 <+> parensIf useRight doc2
          where
            useRight = 
                case project t2 of
                    TApp{} -> True
                    TArr{} -> True
                    _      -> False

        TVar _ var -> pretty var
        TCon _ con -> pretty con

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Pretty a) => Pretty (PredicateT a) where
    pretty (InClass n t) = pretty n <+> pretty t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Scheme where
    pretty _ = "TODO"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

parensIf :: Bool -> Doc a -> Doc a
parensIf isTrue doc = if isTrue then parens doc else doc

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

prettyList_ :: [Doc a] -> Doc a
prettyList_ = brackets . commaSep

prettyRow :: Doc a -> Row (Doc a) -> Doc a
prettyRow delim row@(Row map r) = body <> leaf where

    leaf = case r of
        Nothing -> ""
        Just q -> " " <> pipe <+> pretty q

    body = case rowType row of
        RNil     -> "{}"
        RVar var -> pretty var
        RExt     -> fields (elm <$> Map.toList map)

    elm (k, es) = fields ((\y -> pretty k <+> delim <+> y) <$> es)
    fields f    = mconcat (intersperse ", " f)

--prettyRow2 :: (Pretty e) => Doc a -> Row e -> Doc a
--prettyRow2 delim row = prettyRow delim (pretty <$> row)
--
--prettyRow2 delim row@(Row map r) =
--    case rowType row of
--        RNil     -> "{}"
--        RVar var -> pretty var
--        RExt     -> fields (elm <$> Map.toList map)
--  where
--    elm (k, es) = fields ((\y -> pretty k <+> delim <+> pretty y) <$> es)
--    fields f    = mconcat (intersperse ", " f)

--prettyRow :: (Pretty e) => Doc a -> Row e -> Doc a
--prettyRow delim row =
--    case project row of
--        RNil     -> "{}"
--        RVar var -> pretty var
--        _        -> "{" <+> body <+> "}"
--  where
--    body = (`para` row) $ \case
--        RNil             -> ""
--        RVar var         -> pretty var
--        RExt label e row -> pretty label <+> delim <+> pretty e <> next row
--
--    next :: (Row e, Doc a) -> Doc a
--    next (row, doc) =
--        case project row of
--            RNil     -> ""
--            RVar var -> " |" <+> pretty var
--            _        -> comma <+> doc
