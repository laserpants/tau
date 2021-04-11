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
import Tau.Compiler.Substitution hiding (null)
import Tau.Lang
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
        PCon _ con ps -> pretty con <+> foldr pCon "" ps

        expr -> snd <$> expr & \case
            PVar    _ var    -> pretty var
            PLit    _ prim   -> pretty prim
            PAs     _ name p -> p <+> "as" <+> pretty name
            POr     _ p q    -> p <+> "or" <+> q
            PAny    _        -> "_"
            PTuple  _ ps     -> prettyTuple ps
            PList   _ ps     -> prettyList_ ps
            PRecord _ row    -> lbrace <+> prettyRow "=" row <+> rbrace

pCon :: (ProgPattern t, Doc a) -> Doc a -> Doc a
pCon (p1, doc1) doc2 =
    parensIf useLeft doc1 <> if "" == show doc2 then doc2 else space <> doc2
  where
    useLeft = case project p1 of
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
        ECon    _ name es        -> "TODO"
        EApp    _ es             -> prettyApp (fst <$> es)
        EFix    _ name e1 e2     -> "TODO"
        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
        EPat    _ es cs          -> "TODO"
        EFun    _ cs             -> "TODO"

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

instance (Pretty b) => Pretty (Binding b) where
    pretty = \case
        BLet pat  -> pretty pat
        BFun f ps -> pretty f <> prettyTuple (pretty <$> ps)

prettyApp :: (Pretty p) => [p] -> Doc a
prettyApp (f:args) = pretty f <> prettyTuple (pretty <$> args)

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

instance (Typed t) => Pretty (Ast t) where
    pretty (Ast expr) = pretty (showTree tree)
      where
        tree = unpack . renderDoc <$> exprTree expr

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

exprTree :: (Typed t) => ProgExpr t -> Tree (Doc a)
exprTree = para $ \case

    EVar    t var        -> Node (pretty var <+> colon <+> pretty (typeOf t)) []
    ECon    t name es    -> Node "TODO" []
    ELit    t prim       -> Node (pretty prim <+> colon <+> pretty (typeOf t)) []
    EApp    t es         -> Node (pretty (appExpr t (fst <$> es)) <+> colon <+> pretty (typeOf t)) []
    ELet    t bind e1 e2 -> letTree t bind (snd e1) (snd e2)
    EFix    t name e1 e2 -> Node "TODO" []
    ELam    t ps e       -> Node "TODO" []
    EIf     t e1 e2 e3   -> Node "TODO" []
    EPat    t es cs      -> Node "TODO" []
    EFun    t cs         -> Node "TODO" []
    EOp1    t op a       -> op1Tree t op (snd a)
    EOp2    t op a b     -> op2Tree t op (snd a) (snd b)
    ETuple  t es         -> Node "TODO" []
    EList   t es         -> Node "TODO" []
    ERecord t row        -> Node "TODO" []

op1Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a)
op1Tree t op a = Node (pretty op <+> colon <+> pretty (typeOf t)) [a]

op2Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
op2Tree t op a b = Node ("(" <> pretty op <> ")" <+> colon <+> pretty (typeOf t)) [a, b]

letTree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
letTree t bind e1 e2 =
    Node ("let" <+> colon <+> pretty (typeOf t))
        [ Node (pretty bind <+> equals) [e1]
        , Node "in" [e2]
        ]
