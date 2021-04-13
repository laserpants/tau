{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where

import Control.Arrow ((<<<), (>>>))
import Control.Monad ((<=<))
import Data.Function ((&))
import Data.List (null, intersperse)
import Data.Text (pack, unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Tau.Compiler.Error
import Tau.Compiler.Substitution hiding (null)
import Tau.Lang
import Tau.Prog
import Tau.Row
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Prim where
    pretty = \case
        TUnit      -> "()"
        TBool b    -> pretty b
        TInt n     -> pretty n
        TInteger n -> pretty n
        TFloat f   -> pretty f
        TDouble d  -> pretty d
        TChar c    -> squotes (pretty c)
        TString s  -> dquotes (pretty s)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Eq e, Pretty e) => Pretty (Row e) where
    pretty (Row map r) | null map = maybe "{}" pretty r
    pretty row =
        lbrace <+> prettyRow ":" (pretty <$> row) <+> rbrace

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (ProgPattern t) where
    pretty = para $ \case

        PCon _ con [] -> pretty con
        PCon _ con ps -> pretty con <+> foldr pCon "" (fst <$> ps)

        expr -> snd <$> expr & \case
            PVar    _ var    -> pretty var
            PLit    _ prim   -> pretty prim
            PAs     _ name p -> p <+> "as" <+> pretty name
            POr     _ p q    -> p <+> "or" <+> q
            PAny    _        -> "_"
            PTuple  _ ps     -> prettyTuple ps
            PList   _ ps     -> prettyList_ ps
            PRecord _ row    -> lbrace <+> prettyRow "=" row <+> rbrace

pCon :: ProgPattern t -> Doc a -> Doc a
pCon pat doc = lhs <> rhs
  where
    lhs = parensIf useLeft (pretty pat)
    rhs = if "" == show doc then "" else space <> doc
    useLeft = case project pat of
        PCon _ _ ps | not (null ps) -> True
        PAs{}                       -> True
        POr{}                       -> True
        _                           -> False

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Kind where
    pretty = para $ \case
        KArr (k1, doc1) (_, doc2) -> parensIf useLeft doc1 <+> "->" <+> doc2
          where
            useLeft =
                case project k1 of
                    KArr{} -> True
                    _      -> False

        KTyp   -> "*"    -- Value type
        KClass -> "!"    -- Type class constraint
        KRow   -> "row"  -- Row type

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Type where
    pretty ty =
        case innermostCon ty of
            Just con | isTuple con -> prettyTupleType ty
            Just "#Record"         -> prettyRecordType ty
            _                      -> prettyType ty

prettyTupleType :: Type -> Doc a
prettyTupleType ty = let (_:ts) = unfoldApp ty in prettyTuple (pretty <$> ts)

prettyRecordType :: Type -> Doc a
prettyRecordType = project >>> \case
    TApp (Fix (TCon _ "#Record")) row ->
        lbrace <+> prettyRow ":" (pretty <$> typeToRow row) <+> rbrace

prettyType :: Type -> Doc a
prettyType = para $ \case

    TArr (t1, doc1) (_, doc2) -> parensIf useLeft doc1 <+> "->" <+> doc2
      where
        useLeft =
            case project t1 of
                TArr{} -> True
                _      -> False

    TApp (_, doc1) (t2, doc2) -> doc1 <+> parensIf useRight doc2
      where
        useRight =
            case project t2 of
                TApp{} -> True
                TArr{} -> True
                _      -> False

    TVar _ var -> pretty var
    TCon _ con -> pretty con

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Pretty a) => Pretty (PredicateT a) where
    pretty (InClass n t) = pretty n <+> pretty t

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Scheme where
    pretty _ = "TODO"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Pretty t) => Pretty (Substitution t) where
    pretty _ = "TODO"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

parensIf :: Bool -> Doc a -> Doc a
parensIf isTrue doc = if isTrue then parens doc else doc

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

prettyList_ :: [Doc a] -> Doc a
prettyList_ = brackets . commaSep

prettyRow :: Doc a -> Row (Doc a) -> Doc a
prettyRow delim row@(Row map r) = body <> leaf where

    leaf = case r of
        Nothing -> ""
        Just q -> " " <> pipe <+> pretty q

    body = case rowType row of
        RNil     -> "{}"
        RVar var -> pretty var
        RExt     -> fields (elm <$> Map.toList map)

    elm (k, es) = fields ((\y -> pretty k <+> delim <+> y) <$> es)
    fields f    = mconcat (intersperse ", " f)

unfoldApp :: Type -> [Type]
unfoldApp = para $ \case
    TApp (_, a) (_, b) -> a <> b
    TArr (a, _) (b, _) -> [tArr a b]
    TCon k c           -> [tCon k c]
    TVar k v           -> [tVar k v]

innermostCon :: Type -> Maybe Name
innermostCon = cata $ \case
    TCon _ con -> Just con
    TApp a _   -> a
    _          -> Nothing

isTuple :: Name -> Bool
isTuple con = Just True == (allCommas <$> stripped con)
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (ProgExpr t) where
    pretty = para $ \case
        ECon    _ con []         -> pretty con
        ECon    _ con es         -> pretty con <+> foldr eCon "" (fst <$> es)
        EApp    _ es             -> prettyApp (fst <$> es)
        EFix    _ name e1 e2     -> "fix TODO"
        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
        EFun    _ cs             -> "fun" <+> pipe <+> prettyClauses (fst <$$> cs)
        EPat    _ [e] cs         -> "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)

        expr -> snd <$> expr & \case

            EVar    _ var        -> pretty var
            ELit    _ prim       -> pretty prim
            ELet    _ bind e1 e2 -> "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
            EOp1    _ op a       -> pretty op <+> a
            EOp2    _ op a b     -> a <+> pretty op <+> b
            ETuple  _ es         -> prettyTuple es
            EList   _ es         -> prettyList_ es
            ERecord _ row        -> lbrace <+> prettyRow "=" row <+> rbrace

instance (Pretty b) => Pretty (Binding t b) where
    pretty = \case
        BLet _ pat  -> pretty pat
        BFun _ f ps -> pretty f <> prettyTuple (pretty <$> ps)

prettyApp :: (Pretty p) => [p] -> Doc a
prettyApp (f:args) = pretty f <> prettyTuple (pretty <$> args)

instance (Pretty a) => Pretty (Clause t (ProgPattern t) a) where
    pretty (Clause t ps gs) = pats <> guards
      where
        pats   | 1 == length ps = pretty (head ps)
               | otherwise      = foldr pCon "" ps 
        guards | null gs        = ""
               | otherwise      = commaSep (pretty <$> gs)

instance (Pretty a) => Pretty (Guard a) where
    pretty (Guard es e) = iffs <+> "=>" <+> pretty e
      where
        iffs | null es = ""
             | otherwise = space <> "iff" <+> commaSep (pretty <$> es) 

prettyClauses :: (Pretty p) => [p] -> Doc a
prettyClauses cs = hsep (punctuate (space <> pipe) (pretty <$> cs))

{-
  match xs with
    | Some y 
      iff y > 10 => 1
      iff y < 2  => 2
      otherwise  => 3
-}

eCon :: ProgExpr t -> Doc a -> Doc a
eCon expr doc = lhs <> rhs
  where
    lhs = parensIf useLeft (pretty expr)
    rhs = if "" == show doc then "" else space <> doc
    useLeft = case project expr of
        ECon _ _ es | not (null es) -> True
        ELam{}                      -> True
        _                           -> False

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (Op1 t) where
    pretty _ = "TODO"

instance Pretty (Op2 t) where
    pretty = \case

        OEq     _ -> "=="
        ONeq    _ -> "/="
        OAnd    _ -> "&&"
        OOr     _ -> "||"
        OAdd    _ -> "+"
        OSub    _ -> "-"
        OMul    _ -> "*"
        ODiv    _ -> "/"
        OPow    _ -> "^"
        OMod    _ -> "%"
        OLt     _ -> "<"
        OGt     _ -> ">"
        OLte    _ -> "<="
        OGte    _ -> ">="
        OLarr   _ -> "<<"
        ORarr   _ -> ">>"
        OFpipe  _ -> "|>"
        OBpipe  _ -> "<|"
        OOpt    _ -> "?"
        OStrc   _ -> "++"
        ONdiv   _ -> "//"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Typed t, Pretty t) => Pretty (Ast t) where
    pretty (Ast expr) = pretty (showTree tree)
      where
        tree = unpack . renderDoc <$> exprTree expr

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

exprTree :: (Typed t, Pretty t) => ProgExpr t -> Tree (Doc a)
exprTree = para $ \case

    EVar    t var        -> Node (annotated t var) []
    ECon    t con es     -> Node (annotated t con) (snd <$> es)
    ELit    t prim       -> Node (annotated t prim) []
    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) -- (annotated t (appExpr t (fst <$> es))) []
    ELet    t bind e1 e2 -> letTree t bind (snd e1) (snd e2)
    EFix    t name e1 e2 -> Node "fix TODO" []
    ELam    t ps e       -> Node "lam TODO" []
    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
    EPat    t es cs      -> Node (xyz t es) (clauseTree <$> (fst <$$> cs))
    EFun    t cs         -> Node (annotated t ("fun" :: Text)) (clauseTree <$> (fst <$$> cs))
    EOp1    t op a       -> op1Tree t op (snd a)
    EOp2    t op a b     -> op2Tree t op (snd a) (snd b)
    ETuple  t es         -> Node "tuple TODO" []
    EList   t es         -> Node (pretty t) (snd <$> es)
    ERecord t row        -> Node "record TODO" []

xyz t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t

annotated :: (Pretty t, Pretty p) => t -> p -> Doc a
annotated t p = pretty p <+> colon <+> pretty t

withTag :: (Typed t) => ProgExpr t -> Doc a
withTag e = annotated (typeOf (exprTag e)) e 

clauseTree :: (Typed t, Pretty t) => Clause t (ProgPattern t) (ProgExpr t) -> Tree (Doc a)
clauseTree (Clause t ps gs) = Node (pats <+> colon <+> pretty t) (guard <$> gs) 
  where
    pats | 1 == length ps = pretty (head ps)
         | otherwise      = foldr pCon "" ps 
    guard (Guard es e) = Node (commaSep (iff <$> es) <> "=>" <+> withTag e) []
    iff e = "iff" <+> pretty e <> space

--op1Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a)
op1Tree t op a = Node (annotated t op) [a]

--op2Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
op2Tree t op a b = Node ("(" <> pretty op <> ")" <+> colon <+> pretty t) [a, b]

--letTree :: (Pretty p, Typed a1, Typed a2) => a1 -> Binding a2 p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
letTree t bind e1 e2 =
    Node (annotated t ("let" :: Text))
        [ Node (annotated (bindingTag bind) bind <+> equals) [e1]
        , Node "in" [e2]
        ]

ifTree t e1 e2 e3 =
    Node (annotated t ("if" :: Text))
        [ e1 
        , Node "then" [e2]
        , Node "else" [e3]
        ]

instance Pretty (TypeInfoT [Error] Type) where
    pretty (TypeInfo t ps es) = pretty t <> preds <> errs
      where
        preds | null ps   = ""
              | otherwise = space <> pretty ps
        errs  | null es   = ""
              | otherwise = space <> pretty es

instance Pretty Error where
    pretty = pretty . show 
