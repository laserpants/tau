{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where

import Data.Text.Prettyprint.Doc
import Tau.Type
import Tau.Tool

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Kind where
    pretty = para $ \case
        KArr (k1, doc1) (_, doc2) -> parensIf useLeft doc1 <+> "->" <+> doc2
          where
            useLeft = 
                case project k1 of
                    KArr{} -> True
                    _      -> False

        KTyp   -> "*"
        KClass -> "#"
        KRow   -> "r"


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
