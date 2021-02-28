{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Pretty where

import Control.Arrow ((>>>))
import Control.Monad
import Data.List (unfoldr)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Tuple.Extra (both)
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import qualified Data.Text as Text

class Parens t where
    needsParens :: t -> Bool

instance Parens Type where
    needsParens = project >>> \case
        TApp{} -> True
        TArr{} -> True
        _      -> False

instance Parens Kind where
    needsParens = project >>> \case
        KArr{} -> True
        _      -> False

instance Parens (Pattern t) where
    needsParens = project >>> \case
        PCon _ _ [] -> False
        PCon{}      -> True
        PAs{}       -> True
        POr{}       -> True
        _           -> False

instance Parens (Expr t p q r) where
    needsParens = project >>> \case
        ECon _ _ [] -> False
        ECon{}      -> True
        _           -> False

addParens :: (Parens t) => t -> Doc a -> Doc a
addParens a doc = if needsParens a then parens doc else doc

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
        TApp (t1, doc1) (t2, doc2)
            | isTupleCon t1 ->
                let (_:ts) = unfoldApp (tApp t1 t2)
                 in parens (commaSep (pretty <$> ts))
            | isRecordCon t1 ->
                let (Fix (TCon _ con):ts) = unfoldApp (tApp t1 t2)
                    ns = recordFieldNames con
                 in prettyRecord colon (fieldSet (uncurry (Field ()) <$> zip ns (pretty <$> ts)))
            | otherwise ->
                doc1 <+> addParens t2 doc2

        TArr (t1, doc1) (_, doc2) -> addParens t1 doc1 <+> "->" <+> doc2

        TCon _ name -> pretty name
        TVar _ name -> pretty name

leftmost :: (Name -> Bool) -> Type -> Bool
leftmost test = cata $ \case
    TCon _ con -> test con
    TApp a _   -> a
    _          -> False

isTupleCon :: Type -> Bool
isTupleCon = leftmost (\con -> Just True == (allCommas <$> stripped con))
  where
    allCommas = Text.all (== ',')
    stripped = Text.stripSuffix ")" <=< Text.stripPrefix "("

isRecordCon :: Type -> Bool
isRecordCon = leftmost ((==) ("{", "}") . fstLst)
  where
    fstLst ""  = ("", "")
    fstLst con = both Text.singleton (Text.head con, Text.last con)

unfoldApp :: Type -> [Type]
unfoldApp = para alg
  where
    alg (TApp (_, a) (_, b)) = a <> b
    alg (TArr (a, _) (b, _)) = [tArr a b]
    alg (TCon k c) = [tCon k c]
    alg (TVar k v) = [tVar k v]

unfoldArr :: Type -> [Type]
unfoldArr = para alg
  where
    alg (TArr (_, a) (_, b)) = a <> b
    alg (TApp (a, _) (b, _)) = [tApp a b]
    alg (TCon k c) = [tCon k c]
    alg (TVar k v) = [tVar k v]

instance Pretty Kind where
    pretty = para $ \case
        KTyp -> "*"
        KCls -> "#"
        KArr (k1, doc1) (_, doc2) -> addParens k1 doc1 <+> "->" <+> doc2

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var            -> pretty var
        PCon _ "(::)" [x, xs] -> pretty (fst x) <+> "::" <+> pretty (fst xs)
        PCon _ con []         -> pretty con
        PCon _ con ps         -> foldl patternConArg (pretty con) ps
        PLit _ lit            -> pretty lit
        PRec _ fields         -> prettyRecord equals (snd <$> fields)
        PAs  _ name p         -> pretty (fst p) <+> "as" <+> pretty name
        POr  _ p1 p2          -> pretty (fst p1) <+> "or" <+> pretty (fst p2)
        PAny _                -> "_"

patternConArg :: Doc a -> (Pattern t, Doc a) -> Doc a
patternConArg out (pat, doc) = out <+> addParens pat doc 

instance Pretty (Expr t p q r) where
    pretty = para $ \case
        EVar _ var            -> pretty var
        ELit _ lit            -> pretty lit
        ECon _ "(::)" [x, xs] -> pretty (fst x) <+> "::" <+> pretty (fst xs)
        ECon _ con []         -> pretty con
        ECon _ con args       -> foldl conArg (pretty con) args
        _                     -> "TODO"
--        EApp t [a]              
--        ELet t q a a            
--        EFix t Name a a         
--        ELam t r a              
--        EIf  t a a a            
--        EPat t [a] [Clause p a] 
--        EOp1 t Op1 a            
--        EOp2 t Op2 a a          
--        EDot t Name a           
--        ERec t (FieldSet t a)   
--        ETup t [a]              

conArg :: Doc a -> (Expr t p q r, Doc a) -> Doc a
conArg out (expr, doc) = out <+> addParens expr doc 

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

--prettyTuple :: [Doc a] -> Doc a
--prettyTuple = parens . commaSep

prettyRecord :: Doc a -> FieldSet t (Doc a) -> Doc a
prettyRecord sep fset
    | null fields = braces ""
    | otherwise   = lbrace <+> commaSep (prettyField <$> fields) <+> rbrace
  where
    fields = fieldList fset
    prettyField (_, key, val) = pretty key <+> sep <+> val
