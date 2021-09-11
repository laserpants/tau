{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Prettyprinters where

import Control.Arrow ((<<<), (>>>))
import Control.Monad
import Data.Fix (Fix(..))
import Data.Function ((&))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.List (intercalate, intersperse)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Tau.Misc
import Tau.Tree
import Tau.Util
import TextShow
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
encloseSpace l r d = l <+> d <+> r

instance Pretty Prim where
    pretty = \case
        TUnit       -> "()"
        TBool True  -> "true"
        TBool False -> "false"
        TInt     a  -> pretty a
        TBig     a  -> pretty a
        TNat     a  -> pretty a
        TFloat   a  -> pretty a
        TDouble  a  -> pretty a
        TChar    a  -> squotes (pretty a)
        TString  a  -> dquotes (pretty a)
        TSymbol  a  -> pretty a

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
            prettyRecordType t2

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

prettyRecordType :: Type -> Doc a
prettyRecordType t =
    --
    -- Record types
    --
    if null fields
        then maybe "{}" (wrapped "{" "}") final
        else "{" <+> commaSep fields <+> maybe "}" (wrapped "|" "}") final
  where
    wrapped p q = encloseSpace p q . pretty

    fields = flip para t $ \case
        TRow label ty rest -> pretty label <+> ":" <+> pretty (fst ty):snd rest
        _                  -> []

    final = flip cata t $ \case
        TRow _ _ r         -> r
        TVar _ v           -> Just v
        _                  -> Nothing

instance Pretty (PredicateF Name) where
    pretty (InClass n t) = pretty n <+> pretty t

instance Pretty Predicate where
    pretty (InClass n t) = pretty n <+> parensIf (parensRequired t) (pretty t)
      where
        parensRequired = project >>> \case
            TApp{} -> True
            TArr{} -> True
            _      -> False

--isRecordType :: Type -> Bool
--isRecordType = cata $ \case
--    TCon _ c | "#" == c -> True
--    TApp _ a _ -> a
--    _          -> False

instance Pretty Product where
    pretty (Mul con types) = pretty con <> rhs
      where
        rhs
          | null types = ""
          | otherwise  = " " <> hsep (prettyType <$> types)
        prettyType t = parensIf (parensRequired t) (pretty t)
        parensRequired = project >>> \case
            TApp _ a _ | isRecordType a -> False
            TApp{} -> True
            _      -> False

instance Pretty Typedecl where
    pretty (Sum con vars prods) =
        case prods of
            []   -> lhs
            [p]  -> lhs <+> "=" <+> pretty p
            p:ps -> group (lhs <+> nest 2 (line' <> vsep (pre "=" p:(pre "|" <$> ps))))
      where
        pre a p = a <+> pretty p
        lhs = "type"
            <+> pretty con
            <> if null vars then "" else " " <> hsep (pretty <$> vars)

prettyRecord :: [Either (Name, Doc a) (Doc a)] -> Doc a
prettyRecord [] = "{}"
prettyRecord es = group (cat (fn <$> zip [0..] es) <+> "}")
  where
    fn (n, Left (lab, doc)) =
        (if 0 == n then "{" else ",") <+> pretty lab <+> "=" <+> doc

    fn (_, Right doc) = flatAlt "|" " |" <+> doc

instance (Pretty t4) => Pretty (Pattern t1 t2 t3 t4) where
    pretty = para $ \case

        PCon _ "(::)" [hd, tl]           -> snd hd <+> "::" <+> snd tl
        PCon _ con []                    -> pretty con
        PCon _ con ps                    -> pretty con <> align (tupled (snd <$> ps))

        PRecord _ r                      -> prettyRecord (unfoldRow (fst r))

        pat -> snd <$> pat & \case
            PVar    _ var                -> pretty var
            PLit    _ prim               -> pretty prim
            PAs     _ name p             -> p <+> "as" <+> pretty name
            POr     _ p q                -> p <+> "or" <+> q
            PAny    _                    -> "_"
            PTuple  _ ps                 -> tupled ps
            PList   _ ps                 -> list ps
            PAnn    t p                  -> p <+> ":" <+> pretty t
            PRow{}                       -> "???"

      where
        unfoldRow = para $ \case

            PRow _ lab p r               -> Left (lab, pretty (fst p)):snd r
            PCon{}                       -> []
            p                            -> [Right (pretty (embed (fst <$> p)))]

instance Pretty (PatternLight t) where
    pretty (SCon _ con []) = pretty con
    pretty (SCon _ con ps) = prettyTuple (pretty <$> ps)

instance Pretty (Op1 t) where
    pretty = \case
        ONeg    _ -> "-"
        ONot    _ -> "not"

instance Pretty (Op2 t) where
    pretty = pretty . op2Symbol

instance (Pretty u) => Pretty (Binding t (Pattern t t t u)) where
    pretty = \case
        BPat _ p    -> pretty p
        BFun _ f ps -> pretty f <> prettyArgs ps
          where
            prettyArgs [Fix (PLit _ TUnit)] = "()"
            prettyArgs args = align (tupled (pretty <$> args)) -- funArgs args -- parens (commaSep (pretty <$> args))

class FunArgs f where
    funArgs :: f -> Doc a

instance FunArgs Text where
    funArgs = pretty

instance (Pretty u) => FunArgs [ProgPattern t u] where
    funArgs [p] = parensIf (parensRequired p) (pretty p)
      where
        parensRequired = project >>> \case
            PVar{} -> False
            PLit{} -> False
            _      -> True

    funArgs ps = align (tupled (pretty <$> ps))

instance (FunArgs e1, Functor e2, Functor e4, Pretty e3, Pretty t4, Pretty (e2 (Expr t1 t2 t3 t4 e1 e2 e3 e4)), Pretty (e4 (Expr t1 t2 t3 t4 e1 e2 e3 e4))) => Pretty (Expr t1 t2 t3 t4 e1 e2 e3 e4) where
    pretty = para $ \case

        ECon _ "(::)" [hd, tl]           -> snd hd <+> "::" <+> snd tl
        ECon _ con []                    -> pretty con
        ECon _ con ps                    -> pretty con <> align (tupled (snd <$> ps)) -- prettyTuple (snd <$> ps)

        EApp _ ((e, doc1):es) ->
            parensIf parensRequiredL doc1 <> prettyArgs es
          where
            prettyArgs [(Fix (ELit _ TUnit), _)] = "()"
            -- prettyArgs args = parens (commaSep (snd <$> args))
            prettyArgs args = align (tupled (snd <$> args))

            parensRequiredL =
                case project e of
                    EVar{} -> False
                    _      -> True

        ERecord _ r                      -> prettyRecord (unfoldRow (fst r))
        ECodata _ e                      -> "::TODO::"
        ELam    _ ps e                   -> prettyLam (funArgs ps) (snd e)
        ELet    _ bind e1 e2             -> prettyLet "let" (pretty bind) (letRhs e1) (snd e2)
        EFix    _ name e1 e2             -> prettyLet "fix" (pretty name) (snd e1) (snd e2)
        EPat    _ e1 cs                  -> group (nest 2 (vsep ["match" <+> snd e1 <+> "with", clauses1 (fst <$$> cs)]))
        EFun    _ cs                     -> group (clauses (fst <$$> cs))

        expr -> snd <$> expr & \case
            EVar    _ var                -> pretty var
            EHole   _                    -> "_"
            ELit    _ prim               -> pretty prim
            EIf     _ e1 e2 e3           -> prettyIf e1 e2 e3
            EOp1    _ op a               -> pretty op <> a
            EOp2    _ (ODot _) a b       -> b <> "." <> a
            EOp2    _ (OField _) a b     -> b <> "." <> a
            EOp2    _ op a b             -> a <+> pretty op <+> b
            ETuple  _ es                 -> tupled es
            EList   _ es                 -> list es
            EAnn    t e                  -> e <+> ":" <+> pretty t
            ERow{}                       -> "???"

      where
        unfoldRow = para $ \case

            ERow _ lab e r               -> Left (lab, pretty (fst e)):snd r
            ECon{}                       -> []
            e                            -> [Right (pretty (embed (fst <$> e)))]

prettyIf :: Doc a -> Doc a -> Doc a -> Doc a
prettyIf e1 e2 e3 =
    "if" <> softline <> e1 <> space <> group (nest 2 (line' <> vsep
        [ group (nest 2 (vsep ["then", e2]))
        , group (nest 2 (vsep ["else", e3]))
        ]))

prettyLam :: Doc a -> Doc a -> Doc a
prettyLam args body = group (nest 2 (vsep [args <+> "=>", body]))

prettyLet :: Doc a -> Doc a -> Doc a -> Doc a -> Doc a
prettyLet kword bind e1 e2 =
    group (nest 2 (vsep
        [ kword
        , bind <+> nest 2 e1
        , nest 2 (vsep ["in", e2]) ]))

letRhs :: (FunArgs e1, Functor e2, Functor e4, Pretty e3, Pretty t4, Pretty (e4 (Expr t1 t2 t3 t4 e1 e2 e3 e4))) => (Expr t1 t2 t3 t4 e1 e2 e3 e4, Doc a) -> Doc a
letRhs (expr, doc) =
    case project expr of
        EFun _ cs -> line' <> vsep (pre "|" <$> cs)
        _         -> group (vsep ["=", doc])
  where
    pre a p = a <+> pretty p

clauses1 :: Pretty p => [p] -> Doc a
clauses1 cs = vsep (pre "|" <$> cs)
  where
    pre a p = a <+> pretty p

clauses :: Pretty p => [p] -> Doc a
clauses cs = encloseSep "" "" " | " (pretty <$> cs)

class Patterns p where
    prettyPatterns :: p -> Doc a

instance (Pretty u) => Patterns (ProgPattern t u) where
    prettyPatterns = pretty

instance (Pretty u) => Patterns [ProgPattern t u] where
    prettyPatterns [p] = pretty p
    prettyPatterns ps  = parens (commaSep (pretty <$> ps))

instance (Pretty p, Pretty a, Patterns p) => Pretty (Clause t p a) where
    pretty (Clause _ p cs) = prettyPatterns p <+> prettyChoices cs

instance (Pretty p, Pretty a) => Pretty (MonoClause t p a) where
    pretty (MonoClause _ p cs) = pretty p <+> prettyChoices cs

class Choices c where
    prettyChoices :: c -> Doc a

instance (Pretty a) => Choices (Choice a) where
    prettyChoices (Choice [] e) = "=>" <+> pretty e
    prettyChoices choice = prettyChoice "" choice

instance (Pretty a) => Choices [Choice a] where
    prettyChoices [Choice [] e] = "=>" <+> pretty e
    prettyChoices (c:cs) = line' <> sep (flatAlt (indent 2 zyx) zyx:fmap (prettyChoice ", ") cs)
      where
        zyx = (prettyChoice "" c)

--prettyChoice x (Choice es e) = flatAlt (indent 2 zzz) zzz <+> "=>" <+> pretty e
prettyChoice x (Choice es e) = flatAlt (indent 2 zzz) zzz <+> "=>" <+> pretty e
  where
    zzz = (prettyWhens x es)

prettyWhens :: (Pretty p) => Doc a -> [p] -> Doc a
prettyWhens stor = \case
    [] -> stor <> "otherwise"
    es -> stor <> "when" <> parens (commaSep (pretty <$> es))

instance (Pretty u) => Pretty (Topdecl t u) where
    pretty (Top _ bind@BPat{} expr) =
        case project expr of
            EFun{} -> pretty bind <+> "|" <+> pretty expr
            _      -> pretty bind <+> "=" <+> pretty expr
    pretty (Top _ bind expr) =
        pretty bind <> " =" <+> pretty expr

instance Pretty Scheme where
    pretty (Forall kinds ps ty) = forall <> classes <> pretty (instn ty)
      where
        forall
            | null kinds = ""
            | otherwise  = "forall" <+> sep (pretty <$> take (length kinds) letters) <> ". "
        classes
            | null ps    = ""
            | otherwise  = tupled preds <+> "=> "

        instn = fromPolytype (tVar kTyp <$> letters)
        preds = [pretty c <+> pretty (instn (tGen ty)) | InClass c ty <- ps]

--
--
--

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
            CPat e1 cs                   -> "TODO" -- nest 2 (vsep ["match" <+> e1 <+> "with", coreClauses cs])

--coreClauses cs = vsep (prettyClause <$> cs)
--  where
--    prettyClause (ns, e) = pipe <+> prettyTuple (pretty <$> ns) <+> "=>" <+> e

instance Pretty Error where
    pretty = pretty . show
