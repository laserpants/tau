{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Prettyprinters where

import Control.Arrow ((<<<), (>>>))
import Control.Monad
import Data.Fix (Fix(..))
import Data.Function ((&))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Tau.Misc
import Tau.Tree
import Tau.Util
import qualified Data.Text as Text

parensIf :: Bool -> Doc a -> Doc a
parensIf True doc = parens doc
parensIf _    doc = doc

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

prettyList_ :: [Doc a] -> Doc a
prettyList_ = brackets . commaSep

encloseSpace :: Doc a -> Doc a -> Doc a -> Doc a
encloseSpace a b c = a <+> c <+> b

instance Pretty Prim where
    pretty = \case
        TUnit      -> "()"
        TBool    a -> pretty a
        TInt     a -> pretty a
        TInteger a -> pretty a
        TFloat   a -> pretty a
        TDouble  a -> pretty a
        TChar    a -> squotes (pretty a)
        TString  a -> dquotes (pretty a)
        TSymbol  a -> pretty a

instance Pretty Kind where
    pretty = para $ \case
        KArr (k1, doc1) (_, doc2) ->
            parensIf parensRequiredL doc1 <+> "->" <+> doc2
          where
            parensRequiredL =
                case project k1 of
                    KArr{} -> True
                    _      -> False

        KVar var -> pretty var
        KCon con -> pretty con

instance Pretty Type where
    pretty = para $ \case
        TArr (t1, doc1) (_, doc2) ->
            parensIf parensRequiredL doc1 <+> "->" <+> doc2
          where
            parensRequiredL =
                case project t1 of
                    TArr{} -> True
                    _      -> False

        TApp _ (Fix (TCon _ "#"), _) (t2, _) ->
            if null fields
                then maybe "{}" (wrapped "{" "}") final
                else "{" <+> commaSep fields <+> maybe "}" (wrapped "|" "}") final
          where
            wrapped p q = (encloseSpace p q . pretty)

            fields = flip para t2 $ \case
                TRow label ty rest -> pretty label <+> ":" <+> pretty (fst ty):snd rest
                _                  -> []

            final = flip cata t2 $ \case
                TRow _ _ r         -> r
                TVar _ v           -> Just v
                _                  -> Nothing

        TApp k (t1, _) (t2, _) | isTupleType t1 ->
            let (_:ts) = unfoldApp (tApp k t1 t2)
             in prettyTuple (pretty <$> ts)

        TApp _ (t1, doc1) (t2, doc2) ->
            parensIf parensRequiredL doc1 <+> parensIf parensRequiredR doc2
          where
            parensRequiredL =
                case project t1 of
                    TArr{} -> True
                    _      -> False

            parensRequiredR =
                case project t2 of
                    TApp{} -> True
                    TArr{} -> True
                    TRow{} -> True
                    _      -> False

        TVar _ var -> pretty var
        TCon _ con -> pretty con

        TRow label (t1, doc1) (t2, doc2) ->
            "{" <> pretty label <> "}" <+> parensIf parensRequiredL doc1
                                       <+> parensIf parensRequiredR doc2
          where
            parensRequiredL =
                case project t1 of
                    TArr{} -> True
                    _      -> False

            parensRequiredR =
                case project t2 of
                    TCon _ "{}" -> False
                    TVar{}      -> False
                    _           -> True

instance Pretty (PredicateT Name) where
    pretty (InClass n t) = pretty n <+> pretty t

instance Pretty Predicate where
    pretty (InClass n t) = pretty n <+> parensIf (parensRequired t) (pretty t)
      where
        parensRequired = project >>> \case
            TApp{} -> True
            TArr{} -> True
            _      -> False

instance (Pretty p, Pretty a) => Pretty (Clause t p a) where
    pretty (Clause _ p cs) = pipe <+> pretty p <+> pretty cs

instance (Pretty p, Pretty a) => Pretty (MonoClause t p a) where
    pretty (MonoClause _ p cs) = pipe <+> pretty p <+> pretty cs

instance Pretty (Choice a) where
    pretty (Choice es e) = "TODO"

instance Pretty (Op1 t) where
    pretty = \case
        ONeg    _ -> "-"
        ONot    _ -> "not"

instance Pretty (Op2 t) where
    pretty = pretty . op2Symbol

instance (Pretty t6) => Pretty (Pattern t1 t2 t3 t4 t5 t6) where
    pretty = para $ \case

        PCon _ "(::)" [hd, tl]           -> snd hd <+> "::" <+> snd tl
        PCon _ con []                    -> pretty con
        PCon _ con ps                    -> pretty con <> prettyTuple (snd <$> ps)

        PRecord _ r                      -> prettyRecord (fst r)

        pat -> snd <$> pat & \case
            PVar    _ var                -> pretty var
            PLit    _ prim               -> pretty prim
            PAs     _ name p             -> p <+> "as" <+> pretty name
            POr     _ p q                -> p <+> "or" <+> q
            PAny    _                    -> "_"
            PTuple  _ ps                 -> prettyTuple ps
            PList   _ ps                 -> prettyList_ ps
            PAnn    t p                  -> p <+> ":" <+> pretty t

            _ -> "TODO"

      where
        prettyRecord = project >>> \case
            PVar _ v                     -> pretty v
            r@PRow{}                     -> "{" <+> commaSep (fields (embed r)) <> final (embed r) <+> "}"
            PCon _ "{}" []               -> "{}"
            PCon _ con []                -> pretty con
            PCon _ con ps                -> pretty con <> prettyTuple (pretty <$> ps)

        fields = para $ \case
            PRow _ label p rest          -> pretty label <+> "=" <+> pretty (fst p):snd rest
            _                            -> []

        final = cata $ \case
            PRow _ _ _ r                 -> r
            PVar _ v                     -> " " <> pipe <+> pretty v
            _                            -> ""

instance Pretty (PatternLight t) where
    pretty (SCon _ con []) = pretty con
    pretty (SCon _ con ps) = prettyTuple (pretty <$> ps)

instance (Functor e2, Functor e4, Pretty t11) => Pretty (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 e1 e2 e3 e4) where
    pretty = para $ \case

        ECon _ "(::)" [hd, tl]           -> snd hd <+> "::" <+> snd tl
        ECon _ con []                    -> pretty con
        ECon _ con ps                    -> pretty con <> prettyTuple (snd <$> ps)

        EApp _ ((e, doc1):es) ->

            parensIf parensRequiredL doc1 <> prettyArgs es
          where
            prettyArgs [(Fix (ELit _ TUnit), _)] = "()"
            prettyArgs args = parens (commaSep (snd <$> args))

            parensRequiredL =
                case project e of
                    EVar{} -> False
                    _      -> True

        ERecord _ r                      -> prettyRecord (fst r)

        expr -> snd <$> expr & \case
            EVar    _ var                -> pretty var
            EHole   _                    -> "_"
            ELit    _ prim               -> pretty prim
--            EIf     _ e1 e2 e3           -> prettyIf e1 e2 e3
--            EFix    _ name e1 e2         -> prettyFix name e1 e2
            EOp1    _ op a               -> pretty op <> a
            EOp2    _ (ODot _) a b       -> b <> "." <> a
            EOp2    _ (OField _) a b     -> b <> "." <> a
            EOp2    _ op a b             -> a <+> pretty op <+> b
            ETuple  _ es                 -> prettyTuple es
            EList   _ es                 -> prettyList_ es
            EAnn    t e                  -> e <+> ":" <+> pretty t

            _ -> "TODO"

      where
        prettyRecord = project >>> \case
            EVar _ v                     -> pretty v
            r@ERow{}                     -> "{" <+> commaSep (fields (embed r)) <> final (embed r) <+> "}"
            ECon _ "{}" []               -> "{}"
            ECon _ con []                -> pretty con
            ECon _ con es                -> pretty con <> prettyTuple (pretty <$> es)

        fields = para $ \case
            ERow _ label p rest          -> pretty label <+> "=" <+> pretty (fst p):snd rest
            _                            -> []

        final = cata $ \case
            ERow _ _ _ r                 -> r
            EVar _ v                     -> " " <> pipe <+> pretty v
            EApp _ (_:a:_)               -> a
            _                            -> ""

instance Pretty Core where
    pretty = para $ \case

        CApp ((e, doc1):es) ->
            parensIf parensRequiredL doc1 <> prettyArgs es
          where
            prettyArgs args = parens (commaSep (snd <$> args))

            parensRequiredL =
                case project e of
                    CVar{} -> False
                    _      -> True

        expr -> snd <$> expr & \case

            CVar var                     -> pretty var
            CLit prim                    -> pretty prim
            CLet name e1 e2              -> "TODO" -- prettyLet (pretty name <+> "=") e1 e2
            CLam name e1                 -> "TODO" -- prettyLam (pretty name) e1
            CIf  e1 e2 e3                -> "TODO" -- prettyIf e1 e2 e3
            CPat e1 cs                   -> nest 2 (vsep ["match" <+> e1 <+> "with", coreClauses cs])

coreClauses cs = vsep (prettyClause <$> cs)
  where
    prettyClause (ns, e) = pipe <+> prettyTuple (pretty <$> ns) <+> "=>" <+> e

instance Pretty Product where
    pretty (Mul con types) =
        pretty con <+> hsep (prettyType <$> types)
      where
        prettyType t = parensIf (useParens t) (pretty t)
        useParens = project >>> \case
            TApp _ a _ | isRecordType a -> False
            TApp{} -> True
            TCon{} -> True
            _      -> False

instance Pretty Datatype where
    pretty (Sum con vars prods) =
        case prods of
            []   -> lhs
            [p]  -> lhs <+> "=" <+> pretty p
            p:ps -> lhs <+> nest 2 (line' <> vsep (pre "=" p:(pre "|" <$> ps)))
      where
        pre a p = a <+> pretty p
        lhs = "type"
            <+> pretty con
            <> if null vars then ""
                            else " " <> hsep (pretty <$> vars)

isTupleType :: Type -> Bool
isTupleType = cata $ \case
    TCon _ con -> Just True == (allCommas <$> stripped con)
    TApp _ a _ -> a
    _          -> False
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

isRecordType :: Type -> Bool
isRecordType = cata $ \case
    TCon _ c | "#" == c -> True
    TApp _ a _ -> a
    _          -> False

instance Pretty Error where
    pretty = pretty . show
