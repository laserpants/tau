{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Pretty where

import Control.Arrow ((>>>))
import Control.Monad (join)
import Data.List (sortOn)
import Data.Maybe (fromJust, maybeToList)
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Tuple.Extra (dupe)
import Data.Void
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import Tau.Eval
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
        KTyp     -> "*"
        KArr a b -> cata lhs (fst a) <+> "->" <+> snd b
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
        RCon t con rs -> prettyCon (unlistPrep_ (RCon t con rs)) con (dupe <$> rs) (args . fst) -- prettyCon id con (dupe <$> rs) (args . fst)
      where
        args :: Name -> [Doc a] -> [Doc a]
        args n = (pretty n :)

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var     -> pretty var
        PCon t con ps  -> prettyCon (unlistPat_ (conPat t con (fst <$> ps))) con ps args -- undefined -- prettyCon (concatMap unlistPat) con ps args
        PLit _ lit     -> pretty lit
        PRec _ fields  -> prettyRecord equals (snd <$$> fields)
        PAs  _ name p  -> pretty (fst p) <+> "as" <+> pretty name
        POr  _ p1 p2   -> pretty (fst p1) <+> "or" <+> pretty (fst p2)
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
        ODot   a b -> subOp AssocR b <> dot <> pretty a 
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
                 EOp _ ODot{}        -> pretty a
                 EOp _ ops | par ops -> parens (pretty a)
                 _                   -> pretty a

prettyExpr :: (Pretty p, Pretty q, Pretty (Expr t p q r)) => (r -> Doc a) -> Expr t p q r -> Doc a
prettyExpr f = para $ \case
    EVar _ var     -> pretty var
    ECon t con exs -> prettyCon (unlist_ (conExpr t con (fst <$> exs))) con exs app -- (concatMap unlist) con exs app
    ELit _ lit     -> pretty lit
    EApp _ exs     -> hsep (foldr app [] exs)
    ELet _ p e1 e2 -> prettyLet "let" p e1 e2
    EFix _ n e1 e2 -> prettyLet "fix" n e1 e2
    ELam _ p e1    -> prettyLam (f p) e1
    EIf  _ c e1 e2 -> prettyIf c e1 e2
    EPat _ exs eqs -> prettyMatch exs eqs
    EOp  _ op      -> pretty (fst <$> op)
    ERec _ fields  -> prettyRecord equals (snd <$$> fields)
  where
    app :: (Expr t p q r, Doc a) -> [Doc a] -> [Doc a]
    app a = (rhs :)
      where
        rhs = flip cata (fst a) $ \case
            EApp{}       -> parens (snd a)
            ELam{}       -> parens (snd a)
            EOp _ ODot{} -> snd a
            EOp{}        -> parens (snd a)
            ECon _ _ []  -> snd a
            ECon _ con _ -> 
                if CCons == conType con || CTuple == conType con 
                    then snd a 
                    else parens (snd a)
            _ -> snd a

instance Pretty (Let (Pattern t)) where
    pretty (Let p)       = pretty p
    pretty (LetFun f ps) = pretty f <+> (hsep (fmap ffff ps)) -- hsep (pretty <$> ps)

instance Pretty (PatternExpr t) where
    pretty = prettyExpr (hsep . fmap ffff)

ffff :: Pattern t -> Doc a
ffff p = case project p of
    PCon _ _ [] -> pretty p
    PCon{}      -> parens (pretty p)
    _           -> pretty p

instance (Pretty r) => Pretty (Expr t (Prep t) Name r) where
    pretty = prettyExpr pretty

prettyCon :: (Pretty p) => Maybe [Doc a] -> Name -> [(p, q)] -> ((p, q) -> [Doc a] -> [Doc a]) -> Doc a
prettyCon list con exs fun 
    | null exs      = pretty con

    | CRecord == ct = prettyRecord equals (namesToFields con (pretty . fst <$> exs))
    | CTuple  == ct = prettyTuple (pretty . fst <$> exs)
    | CNil    == ct = "[]"
    | CCons == ct = -- xxx (flatten (fst <$> exs)) -- (pretty <$> flatten (fst <$> exs)) -- "[" <> commaSep (pretty <$> flatten (fst <$> exs)) <> "]"
        case (list, fst <$> exs) of
            (Nothing, [hd, tl]) -> pretty hd <+> "::" <+> pretty tl
            (Just elems, _)     -> "[" <> commaSep elems <> "]"

    | otherwise     = pretty con <+> hsep (foldr fun [] exs)

  where
    ct = conType con

--    yyy [a, b] = traceShow (flatten (fst <$> exs)) ( pretty (fst a) <+> "::" <+> pretty (fst b) )

--prettyCon :: (Pretty p, Show p) => ([p] -> [p]) -> Name -> [(p, q)] -> ((p, q) -> [Doc a] -> [Doc a]) -> Doc a
--prettyCon flatten con exs fun
--    | null exs      = pretty con
--    | CRecord == ct = prettyRecord equals (namesToFields con (pretty . fst <$> exs))
--    | CTuple  == ct = prettyTuple (pretty . fst <$> exs)
--    | CNil    == ct = "[]"
--    | CCons   == ct = yyy exs -- xxx (flatten (fst <$> exs)) -- (pretty <$> flatten (fst <$> exs)) -- "[" <> commaSep (pretty <$> flatten (fst <$> exs)) <> "]"
--    | otherwise     = pretty con <+> hsep (foldr fun [] exs)
--  where
--    ct = conType con
--
--    yyy [a, b] = traceShow (flatten (fst <$> exs)) ( pretty (fst a) <+> "::" <+> pretty (fst b) )

--    xxx [a, b] = pretty a <+> "::" <+> pretty b 
--    xxx xs     = "[" <> commaSep (pretty <$> xs) <> "]"

--unlist :: Expr t p q r -> [Expr t p q r]
--unlist = para $ \case
--    ECon _ "[]"   [] -> []
--    ECon _ "(::)" es -> concat (snd <$> es)
--    e                -> [embed (fst <$> e)]

    --Fix (ECon _ "[]" [])       -> []
    --Fix (ECon _ "(::)" (Fix (ECon _ "(::)" ys):xs)) -> ys <> xs
    --a@(Fix (ECon _ "(::)" _)) -> [a]
    -- x -> []

--unlistPat :: Pattern t -> [Pattern t]
--unlistPat = para $ \case
--    PCon _ "[]"   [] -> []
--    PCon _ "(::)" ps -> concat (snd <$> ps)
--    p                -> [embed (fst <$> p)]

unlist_ :: (Pretty (Expr t p q r)) => Expr t p q r -> Maybe [Doc a] -- Expr t p q r]
unlist_ = \case
    Fix (ECon _ "(::)" (e:es)) -> 
        case sequence (unlist_ <$> es) of
            Just fs -> Just ([pretty e] <> join fs)
            Nothing -> Nothing
    Fix (ECon _ "[]" []) -> Just [] 
    _ -> Nothing

unlistPat_ :: Pattern t -> Maybe [Doc a]
unlistPat_ = \case
    Fix (PCon _ "(::)" (p:ps)) -> 
        case sequence (unlistPat_ <$> ps) of
            Just qs -> Just ([pretty p] <> join qs)
            Nothing -> Nothing
    Fix (PCon _ "[]" []) -> Just [] 
    _ -> Nothing

unlistPrep_ :: Prep t -> Maybe [Doc a]
unlistPrep_ = \case
    RCon _ "(::)" rs -> Just (pretty <$> rs)
    RCon _ "[]" [] -> Just [] 
    _ -> Nothing

unlistValues_ :: Value m -> Maybe [Doc a]
unlistValues_ = \case
    Data "[]"   [] -> Just []
    Data "(::)" (v:vs) -> 
        case sequence (unlistValues_ <$> vs) of
            Just ws -> Just ([pretty v] <> join ws)
            _       -> Nothing
    _ -> Nothing

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
  :: (Pretty p, Pretty q, Pretty s, Pretty (Expr t p q r))
  => Doc a
  -> s
  -> (Expr t p q r, Doc a)
  -> (Expr t p q r, Doc a)
  -> Doc a
prettyLet keyword p e1 e =
    group (vsep
      [ nest 2 (vsep
        [ keyword
        , pretty p <+> equals <+> expr
        , nest 2 (vsep ["in", body])
        ])
      ])
  where
    expr = pretty (fst e1)
    body = pretty (fst e)

-- | Pretty printer for lambda abstractions
prettyLam :: (Pretty (Expr t p q r)) => Doc a -> (Expr t p q r, Doc a) -> Doc a
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

instance Pretty (Value m) where
    pretty = \case
        Closure{}      -> "<<function>>"
        PrimFun{}      -> "<<primitive>>"
        Value lit      -> pretty lit
        Record fields  -> prettyRecord equals (uncurry (Field ()) . fmap pretty <$> fields)
        Data name vals -> prettyCon (unlistValues_ (Data name vals)) name (dupe <$> vals) args
      where
        args :: (Value m, t) -> [Doc a] -> [Doc a]
        args (val, _) = (rhs :)
          where
            rhs = case val of
              Data _ [] -> pretty val
              Data{}    -> parens (pretty val)
              _         -> pretty val

prettyAnnValue :: Value m -> Scheme -> Doc a
prettyAnnValue value scheme = pretty value <+> ":" <+> pretty scheme
