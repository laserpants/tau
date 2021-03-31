{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where

import Control.Arrow ((<<<), (>>>))
import Data.Text.Prettyprint.Doc
import Tau.Lang
import Tau.Tool
import Tau.Type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Eq e, Pretty e) => Pretty (Row e) where
    pretty row =
        case project row of
            RNil     -> "<>"
            RVar var -> pretty var
            _        -> "<" <+> body <+> ">"
      where
        body = (`para` row) $ \case
            RNil             -> ""
            RVar var         -> pretty var
            RExt label e row -> pretty label <+> colon <+> pretty e <> next row

        next :: (Row e, Doc a) -> Doc a
        next (row, doc) =
            case project row of
                RNil     -> ""
                RVar var -> " |" <+> pretty var
                _        -> comma <+> doc

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (ProgPattern t) where
    pretty = undefined

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

parensIf :: Bool -> Doc a -> Doc a
parensIf isTrue doc = if isTrue then parens doc else doc
