{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where

import Data.List (sortOn)
import Data.Maybe (fromJust, maybeToList)
import Data.Text.Prettyprint.Doc
import Data.Void
import Tau.Expr
import Tau.Expr.Main
import Tau.Type
import Tau.Type.Main
import Tau.Util
import qualified Data.Text as Text

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma 

prettyTuple :: [Doc a] -> Doc a
prettyTuple elems = "(" <> commaSep elems <> ")"

prettyRecord :: Doc a -> [Field t (Doc a)] -> Doc a
prettyRecord _ []       = "{}"
prettyRecord sep fields = "{" <+> prettyFields (fieldsInfo fields) <+> "}"
  where
    prettyFields fields = commaSep (field <$> fields)
    field (_, key, val) = pretty key <+> sep <+> val

namesToFields :: Name -> [Doc a] -> [Field () (Doc a)]
namesToFields name = 
    zipWith (Field ()) (concat (maybeToList (Text.split (== ',') <$> stripped)))
  where
    stripped = Text.stripSuffix "}" =<< Text.stripPrefix "{" name

data ConType 
    = TupleCon
    | RecordCon
    | PlainCon
    deriving (Show, Eq)

conType :: Name -> ConType
conType con
    | Text.null con = PlainCon
    | otherwise = 
        case (Text.head con, Text.last con) of
            ('(', ')') -> TupleCon
            ('{', '}') -> RecordCon
            _          -> PlainCon

prettyStructType :: Type v -> Maybe (Doc a)
prettyStructType ty =
   case args ty of
      (a:as) -> headCon (project a) >>= fun (pretty <$> as)
      []     -> Nothing
  where
    fun as con = case conType con of
        TupleCon  -> Just (prettyTuple as)
        RecordCon -> Just (prettyRecord colon (namesToFields con as))
        _         -> Nothing

    headCon (TCon _ c) = Just c
    headCon _          = Nothing

args :: Type v -> [Type v]
args = para $ \case
    TApp a b -> snd a <> [fst b]
    TArr a b -> [tArr (fst a) (fst b)]
    TCon k a -> [tCon k a]
    TVar k a -> [tVar k a]
    _        -> []

instance Pretty (Type v) where
    pretty = para $ \case
        TApp a b -> 
            case prettyStructType (tApp (fst a) (fst b)) of
                Just doc -> doc
                Nothing  -> snd a <+> cata rhs (fst b)
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
        TGen   _    -> ""

instance Pretty Kind where
    pretty = para $ \case
        KTyp -> "*"
        KArr a b  -> cata lhs (fst a) <+> "->" <+> snd b 
          where
            lhs = \case
                KArr{} -> parens (snd a)
                _      -> snd a

instance Pretty (Predicate a) where
    pretty (InClass name ty) = pretty name <+> pretty ty

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

        preds = [pretty c <+> pretty (instt ty) | InClass c ty <- ps]

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
        PCon _ con ps  -> prettyCon con ps args
        PLit _ lit     -> pretty lit
        PRec _ fields  -> prettyRecord equals (fmap snd <$> fields)
        PAny _         -> "_"
      where
        args :: (Pattern t, Doc a) -> [Doc a] -> [Doc a]
        args a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                PCon{}  -> parens (snd a)
                _       -> snd a

instance Pretty (Op (PatternExpr t)) where
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
      where
        binOp a b symb = subOp AssocL a 
                     <+> symb 
                     <+> subOp AssocR b

        subOp :: Assoc -> PatternExpr t -> Doc a
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

instance Pretty (PatternExpr t) where
    pretty = para $ \case
        EVar _ var     -> pretty var
        ECon _ con exs -> prettyCon con exs app
        ELit _ lit     -> pretty lit
        EApp _ exs     -> hsep (foldr app [] exs)
        ELet _ p e1 e2 -> prettyLet p e1 e2
        ELam _ p e1    -> prettyLam p e1 
        EIf  _ c e1 e2 -> prettyIf c e1 e2
        EMat _ exs eqs -> prettyMatch exs eqs
        EOp  _ op      -> pretty (fst <$> op)
        ERec _ fields  -> prettyRecord equals (fmap snd <$> fields)
      where
        app :: (PatternExpr t, Doc a) -> [Doc a] -> [Doc a]
        app a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                EApp{} -> parens (snd a)
                ECon{} -> parens (snd a)
                _      -> snd a

prettyCon :: (Pretty p) => Name -> [(p, q)] -> ((p, q) -> [Doc a] -> [Doc a]) -> Doc a
prettyCon con exs fun
    | null exs        = pretty con
    | RecordCon == ct = prettyRecord equals (namesToFields con (pretty . fst <$> exs))
    | TupleCon  == ct = prettyTuple (pretty . fst <$> exs)
    | otherwise       = pretty con <+> hsep (foldr fun [] exs)
  where
    ct = conType con

prettyMatch 
  :: [(PatternExpr t, Doc a)] 
  -> [Clause (Pattern t) (PatternExpr t, Doc a)] 
  -> Doc a
prettyMatch exs eqs = 
    group (nest 2 (vsep 
        [ "match" <+> commaSep (snd <$> exs) <+> "with"
        , case clause <$> zip lhss rhss of
              []   -> ""
              c:cs -> flatAlt (vsep ((pipe <+>) <$> c:cs)) 
                              (hsep (c:((pipe <+>) <$> cs)))
        ]))
  where
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

-- | Pretty print Let expression
prettyLet 
  :: Pattern t 
  -> (PatternExpr t, Doc a) 
  -> (PatternExpr t, Doc a) 
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

-- | Pretty print Lambda abstraction
prettyLam :: Pattern t -> (PatternExpr t, Doc a) -> Doc a
prettyLam p e1 = 
    group (nest 2 (vsep [backslash <> pattern_ p <+> "=>", pretty (fst e1)]))
  where
    pattern_ :: Pattern t -> Doc a
    pattern_ p = flip cata p $ \case
        PCon _ _ [] -> pretty p
        PCon{}      -> parens (pretty p)
        _           -> pretty p

-- | Pretty print If-clause
prettyIf 
  :: (PatternExpr t, Doc a) 
  -> (PatternExpr t, Doc a) 
  -> (PatternExpr t, Doc a) 
  -> Doc a
prettyIf c e1 e2 = 
    group (nest 2 (vsep [if_, then_, else_]))
  where
    if_   = "if"   <+> pretty (fst c)
    then_ = "then" <+> pretty (fst e1)
    else_ = "else" <+> pretty (fst e2)
