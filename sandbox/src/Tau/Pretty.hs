{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleInstances #-}
module Tau.Pretty where

import Data.Text.Prettyprint.Doc
import Tau.Type
import Tau.Type.Class
import Tau.Util

instance Pretty Type where
    pretty = para $ \case
        TApp a b -> snd a <+> rhs 
          where
            rhs = case project (fst b) of
                TApp{} -> parens (snd b)
                TArr{} -> parens (snd b)
                _      -> snd b
        TArr a b -> lhs <+> "->" <+> snd b 
          where
            lhs = case project (fst a) of
                TArr{} -> parens (snd a)
                _      -> snd a
        TCon _ name -> pretty name
        TVar _ name -> pretty name

instance Pretty Kind where
    pretty = para $ \case
        KStar -> "*"
        KArr a b  -> lhs <+> "->" <+> snd b where
            lhs = case unfix (fst a) of
                KArr{} -> parens (snd a)
                _      -> snd a

instance Pretty Predicate where
    pretty (InClass name ty) = pretty name <+> pretty ty

instance Pretty Scheme where
    pretty scheme = pretty (show baz)
      where baz = flip cata scheme $ \case
              Scheme _      -> []
              Forall _ cs t -> (cs):t

--    pretty scheme = pretty (show ns)
--      where
--        (ty, classes, ns) = flip cata scheme $ \case
--            Scheme t                -> (t, [], 0)
--            Forall _ cs (t, css, n) -> (t, cs:css, succ n)
--

