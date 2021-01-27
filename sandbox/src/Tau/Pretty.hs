{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleInstances #-}
module Tau.Pretty where

import Data.Text.Prettyprint.Doc
import Tau.Expr
import Tau.Type
import Tau.Type.Class
import Tau.Util

prettyType :: [Name] -> Type -> Doc a
prettyType bound = para $ \case
    TApp a b -> snd a <+> cata rhs (fst b)
      where
        rhs = \case
            TApp{} -> parens (snd b)
            TArr{} -> parens (snd b)
            _      -> snd b
    TArr a b -> cata lhs (fst a) <+> "->" <+> snd b 
      where
        lhs = \case
            TArr{} -> parens (snd a)
            _      -> snd a
    TCon _ name -> pretty name
    TVar _ name -> pretty name
    TGen n      -> pretty (bound !! n)

instance Pretty Type where
    pretty = prettyType []

instance Pretty Kind where
    pretty = para $ \case
        KStar -> "*"
        KArr a b  -> cata lhs (fst a) <+> "->" <+> snd b 
          where
            lhs = \case
                KArr{} -> parens (snd a)
                _      -> snd a

instance Pretty Predicate where
    pretty (InClass name ty) = pretty name <+> pretty ty

instance Pretty Scheme where
    pretty scheme = forall <> classes <> prettyType (reverse bound) ty
      where 
        forall
            | null bound = ""
            | otherwise  = "forall " <> sep (pretty <$> bound) <> ". "

        classes
            | null prds = ""
            | otherwise = tupled prds <+> "=> "

        prds = [pretty c <+> pretty n | (n, cs) <- info, c <- cs]

        bound = fst <$> info

        (ty, info) = flip cata scheme $ \case
            Scheme t              -> (t, [])
            Forall _ n cs (s, xs) -> (s, (n, cs):xs)

instance Pretty Literal where
    pretty = \case
        LUnit      -> "()"
        LBool b    -> pretty b
        LInt n     -> pretty n
        LInteger n -> pretty n
        LFloat f   -> pretty f
        LChar c    -> squotes (pretty c)
        LString s  -> dquotes (pretty s)

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var     -> pretty var
        PCon _ con []  -> pretty con
        PCon _ con ps  -> pretty con <+> hsep (foldr args [] ps)
        PLit _ lit     -> pretty lit
        PRec _ fields  -> "{" <+> prettyFields (fmap snd <$> sortFields fields) <+> "}"
        PAny _         -> "_"
      where
        args :: (Pattern t, Doc a) -> [Doc a] -> [Doc a]
        args a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                PCon{}  -> parens (snd a)
                _       -> snd a

prettyFields :: [Field t (Doc a)] -> Doc a
prettyFields fields = hsep (punctuate comma (field <$> fields))
  where
    field (Field _ key val) = pretty key <+> "=" <+> val


