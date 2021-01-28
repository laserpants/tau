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
        PRec _ fields  -> prettyRecord fields
        PAny _         -> "_"
      where
        args :: (Pattern t, Doc a) -> [Doc a] -> [Doc a]
        args a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                PCon{}  -> parens (snd a)
                _       -> snd a

prettyRecord :: [Field t (f, Doc a)] -> Doc a
prettyRecord fields = 
    "{" <+> prettyFields (fmap snd <$> sortFields fields) <+> "}"
  where
    prettyFields fields = 
        hsep (punctuate comma (field <$> fields))
    field (Field _ key val) = 
        pretty key <+> "=" <+> val

instance Pretty (Op (Expr t p q)) where
    pretty op = case op of
        OEq    a b -> binOp a b "=="
        ONEq   a b -> binOp a b "/="
        OAnd   a b -> binOp a b "&&"  
        OOr    a b -> binOp a b "||"  
        OAdd   a b -> binOp a b "+"   
        OSub   a b -> binOp a b "-"
        OMul   a b -> binOp a b "*"
        ODiv   a b -> binOp a b "/"
        OPow   a b -> binOp a b "^"
        OLt    a b -> binOp a b "<"
        OGt    a b -> binOp a b ">"
        OLtE   a b -> binOp a b "<="    
        OGtE   a b -> binOp a b ">="
        OLArr  a b -> binOp a b "<<" 
        ORArr  a b -> binOp a b ">>" 
        OFPipe a b -> binOp a b "|>"
        OBPipe a b -> binOp a b "<|"
        ODot   a b -> pretty a <> "." <> subOp AssocR b
        _          -> undefined
      where
        binOp a b symb = subOp AssocL a 
                     <+> symb 
                     <+> subOp AssocR b

        subOp :: Assoc -> Expr t p q -> Doc a
        subOp assoc a = 
            let par ops = 
                  opPrecedence op >= opPrecedence ops && assoc /= opAssoc op
             in flip cata a $ 
               \case
                 EApp{}              -> parens (pretty a)
                 ELet{}              -> parens (pretty a)
                 ELam{}              -> parens (pretty a)
                 EIf{}               -> parens (pretty a)
                 EOp _ ops | par ops -> parens (pretty a)
                 _                   -> pretty a

instance Pretty (Expr t p q) where
    pretty = para $ \case
        EVar _ var     -> pretty var
        ECon _ con []  -> pretty con
        ECon _ con exs -> pretty con <+> hsep (foldr app [] exs)
        ELit _ lit     -> pretty lit
        EApp _ exs     -> hsep (foldr app [] exs)
        ELet _ p e1 e2 -> ""
        ELam _ p e1    -> ""
        EIf  _ c e1 e2 -> ""
        EMat _ exs eqs -> prettyMatch exs eqs
        EOp  _ op      -> pretty (fst <$> op)
        ERec _ fields  -> prettyRecord fields
      where
        app :: (Expr t p q, Doc a) -> [Doc a] -> [Doc a]
        app a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                EApp{} -> parens (snd a)
                ECon{} -> parens (snd a)
                _      -> snd a

prettyMatch :: [(Expr t p q, Doc a)] -> [Clause p (Expr t p q, Doc a)] -> Doc a
prettyMatch exs eqs = 
    "match" <+> hsep (punctuate comma (snd <$> exs)) <+> "with"

prettyClause :: Clause p x -> Doc a
prettyClause (Clause ps exs e) = ""
