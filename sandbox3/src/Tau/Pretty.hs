{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where
-- Tau.Lang.Pretty

import Control.Arrow ((>>>))
import Data.List (sortOn)
import Data.Maybe (fromJust, maybeToList)
import Data.Maybe (isJust)
import Data.Text.Prettyprint.Doc
import Data.Tuple.Extra (dupe)
import Data.Void
import Tau.Expr
import Tau.Type
import Tau.Util
import qualified Data.Text as Text

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

prettyRecord :: Doc a -> [Field t (Doc a)] -> Doc a
prettyRecord _ []       = braces ""
prettyRecord sep fields = lbrace <+> prettyFields (fieldsInfo fields) <+> rbrace
  where
    prettyFields = commaSep . (field <$>)
    field (_, key, val) = pretty key <+> sep <+> val

namesToFields :: Name -> [Doc a] -> [Field () (Doc a)]
namesToFields name =
    zipWith (Field ()) (concat (maybeToList (Text.split (== ',') <$> stripped)))
  where
    stripped = Text.stripSuffix "}" =<< Text.stripPrefix "{" name

-- TODO: rename
data Constructor
    = CTuple
    | CRecord
    | CNil
    | CCons
    | CPlain
    deriving (Show, Eq)

-- TODO: rename
conType :: Name -> Constructor
conType con
    | Text.null con = CPlain
    | "(::)" == con = CCons
    | "[]"   == con = CNil
    | otherwise =
        case (Text.head con, Text.last con) of
            ('(', ')') -> CTuple
            ('{', '}') -> CRecord
            _          -> CPlain

-- TODO: rename
conType_ :: TypeT v -> Maybe Constructor
conType_ = cata $ \case
    TApp c _ -> c
    TCon _ c -> Just (conType c)
    _        -> Nothing

prettyStructType :: TypeT v -> Maybe (Doc a)
prettyStructType ty =
   case args ty of
      (a:as) -> headCon (project a) >>= fun (pretty <$> as)
      []     -> Nothing
  where
    fun as con = case conType con of
        CTuple  -> Just (prettyTuple as)
        CRecord -> Just (prettyRecord colon (namesToFields con as))
        --CNil    -> Just "CNil"
        --CCons   -> Just "CCons"
        _       -> Nothing

    headCon (TCon _ c) = Just c
    headCon _          = Nothing

args :: TypeT v -> [TypeT v]
args = para $ \case
    TApp a b -> snd a <> [fst b]
    TArr a b -> [tArr (fst a) (fst b)]
    TCon k a -> [tCon k a]
    TVar k a -> [tVar k a]
    _        -> []

instance Pretty (TypeT v) where
    pretty = para $ \case
        TApp a b ->
            case prettyStructType (tApp (fst a) (fst b)) of
                Just doc -> doc
                Nothing  -> snd a <+> cata rhs (fst b)
          where
            con = conType_ (fst b)
            rhs = \case
                TApp{}
                    | isJust con && Just CPlain /= con -> snd b
                    | otherwise -> parens (snd b)
                TArr{} -> parens (snd b)
                _      -> snd b

        TArr a b -> cata lhs (fst a) <+> "->" <+> snd b
          where
            lhs = \case
                TArr{} -> parens (snd a)
                _      -> snd a

        TCon _ name -> pretty name
        TVar _ name -> pretty name
        TGen _      -> ""

instance Pretty Kind where
    pretty = para $ \case
        KTyp -> "*"
        KArr a b  -> cata lhs (fst a) <+> "->" <+> snd b
          where
            lhs = \case
                KArr{} -> parens (snd a)
                _      -> snd a

instance Pretty Predicate where
    pretty (InClass name ty) = pretty (tApp con ty)
      where
        con = tCon (kArr kTyp (fromJust (kindOf ty))) name

instance Pretty Scheme where
    pretty (Forall kinds ps ty) = forall <> classes <> pretty (instt ty)
      where
        names = nameSupply ""
        bound = take (length kinds) names
        instt = replaceBound (tVar kTyp <$> names)

        forall
            | null kinds = ""
            | otherwise  = "forall" <+> sep (pretty <$> bound) <> ". "

        classes
            | null ps    = ""
            | otherwise  = tupled preds <+> "=> "

        preds = [pretty c <+> pretty (instt (tGen ty)) | InClass c ty <- ps]

instance Pretty Literal where
    pretty = \case
        LUnit      -> parens mempty
        LBool b    -> pretty b
        LInt n     -> pretty n
        LInteger n -> pretty n
        LFloat f   -> pretty f
        LChar c    -> squotes (pretty c)
        LString s  -> dquotes (pretty s)

instance Pretty (Prep t) where
    pretty = \case
        RVar _ var    -> pretty var
        RCon _ con rs -> prettyCon id con (dupe <$> rs) (args . fst)
      where
        args :: Name -> [Doc a] -> [Doc a]
        args n = (pretty n :)

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var     -> pretty var
        PCon _ con ps  -> prettyCon (concatMap unlistPat) con ps args
        PLit _ lit     -> pretty lit
        PRec _ fields  -> prettyRecord equals (snd <$$> fields)
        PAny _         -> "_"
      where
        args :: (Pattern t, Doc a) -> [Doc a] -> [Doc a]
        args a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case
                PCon _ _ [] -> snd a
                PCon{}      -> parens (snd a)
                _           -> snd a

instance (Pretty p, Pretty q, Pretty (Expr t p q r)) => Pretty (Op (Expr t p q r)) where
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
        ODot   a b -> pretty a <> dot <> subOp AssocR b
      where
        binOp a b symb = subOp AssocL a
                     <+> symb
                     <+> subOp AssocR b

        subOp :: (Pretty (Expr t p q r)) => Assoc -> Expr t p q r -> Doc a
        subOp assoc a =
            let par ops =
                  case compare (opPrecedence op) (opPrecedence ops) of
                      LT -> False
                      GT -> True
                      EQ -> assoc /= opAssoc op
             in flip cata a $ \case
                 EApp{}              -> parens (pretty a)
                 ELet{}              -> parens (pretty a)
                 ELam{}              -> parens (pretty a)
                 EIf{}               -> parens (pretty a)
                 EOp _ ops | par ops -> parens (pretty a)
                 _                   -> pretty a

prettyExpr :: (Pretty p, Pretty q, Pretty (Expr t p q r)) => (r -> Doc a) -> Expr t p q r -> Doc a
prettyExpr f = para $ \case
    EVar _ var     -> pretty var
    ECon _ con exs -> prettyCon (concatMap unlist) con exs app
    ELit _ lit     -> pretty lit
    EApp _ exs     -> hsep (foldr app [] exs)
    ELet _ p e1 e2 -> prettyLet p e1 e2
    ELam _ p e1    -> prettyLam (f p) e1
    EIf  _ c e1 e2 -> prettyIf c e1 e2
    EMat _ exs eqs -> prettyMatch exs eqs
    EOp  _ op      -> pretty (fst <$> op)
    ERec _ fields  -> prettyRecord equals (snd <$$> fields)
  where
    app :: (Expr t p q r, Doc a) -> [Doc a] -> [Doc a]
    app a = (rhs :)
      where
        rhs = flip cata (fst a) $ \case
            EApp{}       -> parens (snd a)
            ECon _ _ []  -> snd a
            ECon _ con _ -> if CTuple == conType con then snd a else parens (snd a)
            _            -> snd a

instance Pretty (PatternExpr t) where
    pretty = prettyExpr (hsep . fmap f)
      where
        f :: Pattern t -> Doc a
        f p = flip cata p $ \case  -- TODO: use project?
            PCon _ _ [] -> pretty p
            PCon{}      -> parens (pretty p)
            _           -> pretty p

instance (Pretty r) => Pretty (Expr t (Prep t) Name r) where
    pretty = prettyExpr pretty

prettyCon :: (Pretty p) => ([p] -> [p]) -> Name -> [(p, q)] -> ((p, q) -> [Doc a] -> [Doc a]) -> Doc a
prettyCon flatten con exs fun
    | null exs      = pretty con
    | CRecord == ct = prettyRecord equals (namesToFields con (pretty . fst <$> exs))
    | CTuple  == ct = prettyTuple (pretty . fst <$> exs)
    | CNil    == ct = "[]"
    | CCons   == ct = "[" <> commaSep (pretty <$> flatten (fst <$> exs)) <> "]"
    | otherwise     = pretty con <+> hsep (foldr fun [] exs)
  where
    ct = conType con

unlist :: Expr t p q r -> [Expr t p q r]
unlist = para $ \case
    ECon _ "[]"   [] -> []
    ECon _ "(::)" es -> concat (snd <$> es)
    e                -> [embed (fst <$> e)]

unlistPat :: Pattern t -> [Pattern t]
unlistPat = para $ \case
    PCon _ "[]"   [] -> []
    PCon _ "(::)" ps -> concat (snd <$> ps)
    p                -> [embed (fst <$> p)]

prettyMatch :: (Pretty p, Pretty q) => [(a, Doc ann)] -> [Clause p (q, r)] -> Doc ann
prettyMatch exs eqs =
    case exs of
      [] -> impl "fun"
      _  -> impl ("match" <+> commaSep (snd <$> exs) <+> "with")
  where
    impl cmd = group (nest 2 (vsep
        [ cmd
        , case clause <$> zip lhss rhss of
              []   -> ""
              c:cs -> flatAlt (vsep ((pipe <+>) <$> c:cs))
                              (hsep (c:((pipe <+>) <$> cs)))
        ]))

    (lhss, rhss) = unzip (splitClause <$> eqs)
    colWidth     = maximum (length . show <$> lhss)

    clause (lhs, expr) =
        flatAlt (fillBreak colWidth lhs) lhs <+> "=>" <+> expr

splitClause :: (Pretty p, Pretty q) => Clause p (q, r) -> (Doc a, Doc a)
splitClause (Clause ps exs e) =
    ( commaSep (pretty <$> ps) <> when
    , pretty (fst e) )
  where
    when | null exs  = ""
         | otherwise = space <> "when" <+> commaSep (pretty . fst <$> exs)

-- | Pretty printer for let expressions
prettyLet
  :: (Pretty p, Pretty q, Pretty (Expr t p q r))
  => q
  -> (Expr t p q r, Doc a)
  -> (Expr t p q r, Doc a)
  -> Doc a
prettyLet p e1 e =
    group (vsep
      [ nest 2 (vsep
        [ "let"
        , pretty p <+> equals <+> expr
        , nest 2 (vsep ["in", body])
        ])
      ])
  where
    expr = pretty (fst e1)
    body = pretty (fst e)

-- | Pretty printer for lambda abstractions
prettyLam :: (Pretty (Expr t p q r)) => Doc a -> (Expr t p q r, Doc a) -> Doc a
--prettyLam arg e1 = undefined -- group (nest 2 (vsep [backslash <> arg <+> "=>", pretty (fst e1)]))
prettyLam arg e1 = group (nest 2 (vsep [backslash <> arg <+> "=>", pretty (fst e1)]))

-- | Pretty printer for if-clauses
prettyIf
  :: (Pretty p, Pretty q, Pretty (Expr t p q r))
  => (Expr t p q r, Doc a)
  -> (Expr t p q r, Doc a)
  -> (Expr t p q r, Doc a)
  -> Doc a
prettyIf c e1 e2 =
    group (nest 2 (vsep [if_, then_, else_]))
  where
    if_   = "if"   <+> pretty (fst c)
    then_ = "then" <+> pretty (fst e1)
    else_ = "else" <+> pretty (fst e2)
