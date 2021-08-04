{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
module Tau.Prettyprinters where

import Control.Arrow ((<<<), (>>>))
import Control.Monad
import Data.Fix (Fix(..))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Tau.Misc
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

        TRow{} -> "TODO"

--        TRow label (t1, doc1) (t2, doc2) ->
--            "{" <> pretty label <> "}" <+> parensIf parensRequiredL doc1
--                                       <+> parensIf parensRequiredR doc2
--          where
--            parensRequiredL =
--                case project t1 of
--                    TArr{} -> True
--                    _      -> False
--
--            parensRequiredR =
--                case project t2 of
--                    TCon _ "{}" -> False
--                    TVar{}      -> False
--                    _           -> True

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

instance Pretty (Choice a) where
    pretty (Choice es e) = "TODO"

instance Pretty (Op1 t) where
    pretty = \case
        ONeg    _ -> "-"
        ONot    _ -> "not"

instance Pretty (Op2 t) where
    pretty = pretty . op2Symbol

instance Pretty (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10) where
    pretty _ = "TODO"

instance (Functor e2, Functor e4) => Pretty (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4) where
    pretty _ = "TODO"

instance Pretty Product where
    pretty (Mul con types) =
        pretty con <+> hsep (prettyType <$> types)
      where
        prettyType t = parensIf (useParens t) (pretty t)
        useParens = project >>> \case
            TApp _ a _ | isRecordType "#" a -> False
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

isRecordType :: Name -> Type -> Bool
isRecordType con = cata $ \case
    TCon _ c | con == c -> True
    TApp _ a _ -> a
    _          -> False
