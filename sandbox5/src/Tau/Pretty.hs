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
import Tau.Compiler.Substitute hiding (null)
import Tau.Compiler.Translate
import Tau.Compiler.Unify
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
        TBool    a -> pretty a
        TInt     a -> pretty a
        TInteger a -> pretty a
        TFloat   a -> pretty a
        TDouble  a -> pretty a
        TChar    a -> squotes (pretty a)
        TString  a -> dquotes (pretty a)

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--instance (Eq e, Pretty e) => Pretty (Row e) where
--    pretty (Row map r) | null map = maybe "{}" pretty r
--    pretty row = lbrace <+> prettyRow ":" (pretty <$> row) <+> rbrace

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (ProgPattern t) where
    pretty = para $ \case

        PCon _ con [] -> pretty con
        PCon _ con ps -> pretty con <+> foldr patternCon "" (fst <$> ps)

        expr -> snd <$> expr & \case
            PVar    _ var    -> pretty var
            PLit    _ prim   -> pretty prim
            PAs     _ name p -> p <+> "as" <+> pretty name
            POr     _ p q    -> p <+> "or" <+> q
            PAny    _        -> "_"
            PTuple  _ ps     -> prettyTuple ps
            PList   _ ps     -> prettyList_ ps
--            PRecord _ row    -> lbrace <+> prettyRow "=" row <+> rbrace

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Kind where
    pretty = para $ \case
        KArr (k1, doc1) (_, doc2) -> 
            parensIf useLeft doc1 <+> "->" <+> doc2
          where
            useLeft =
                case project k1 of
                    KArr{} -> True
                    _      -> False

        KVar var -> pretty var
        KCon con -> pretty con

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Type where
    pretty ty =
        case innermostCon ty of
            Just con | isTuple con -> prettyTupleType ty
--            Just "#Record"         -> prettyRecordType ty
            _                      -> prettyType ty

prettyTupleType :: Type -> Doc a
prettyTupleType ty = let (_:ts) = unfoldApp ty in prettyTuple (pretty <$> ts)

--prettyRecordType :: Type -> Doc a
--prettyRecordType = project >>> \case
--    TApp (Fix (TCon _ "#Record")) row ->
--        lbrace <+> prettyRow ":" (pretty <$> typeToRow row) <+> rbrace

prettyType :: Type -> Doc a
prettyType = para $ \case

    TArr _ (t1, doc1) (_, doc2) -> 
        parensIf useLeft doc1 <+> "->" <+> doc2
      where
        useLeft =
            case project t1 of
                TArr{} -> True
                _      -> False

    TApp _ (_, doc1) (t2, doc2) -> 
        doc1 <+> parensIf useRight doc2
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

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--instance Pretty Scheme where
--    pretty _ = "TODO"
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--instance (Pretty t) => Pretty (Substitution t) where
--    pretty _ = "TODO"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

parensIf :: Bool -> Doc a -> Doc a
parensIf yes doc = if yes then parens doc else doc

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

prettyList_ :: [Doc a] -> Doc a
prettyList_ = brackets . commaSep

--prettyRow :: Doc a -> Row (Doc a) -> Doc a
--prettyRow delim row@(Row map r) = body <> leaf 
--  where
--    leaf = case r of
--        Nothing -> ""
--        Just q  -> " " <> pipe <+> q
--
--    body = case rowDoc row of
--        RNil     -> "{}"
--        RVar var -> var
--        RExt     -> fields (elm <$> Map.toList map)
--
--    elm (k, es) = fields ((\y -> pretty k <+> delim <+> y) <$> es)
--    fields f    = mconcat (intersperse ", " f)
--
--rowDoc :: Row (Doc a) -> RowType (Doc a)
--rowDoc (Row m Nothing)  | null m = RNil
--rowDoc (Row m (Just r)) | null m = RVar r
--rowDoc _                         = RExt

unfoldApp :: Type -> [Type]
unfoldApp = para $ \case
    TApp _ (_, a) (_, b) -> a <> b
    TArr k (a, _) (b, _) -> [tArr k a b]
    TCon kind con        -> [tCon kind con]
    TVar kind var        -> [tVar kind var]

innermostCon :: Type -> Maybe Name
innermostCon = cata $ \case
    TCon _ con -> Just con
    TApp _ a _ -> a
    _          -> Nothing

isTuple :: Name -> Bool
isTuple con = Just True == (allCommas <$> stripped con)
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----exprCon2 :: SimplifiedExpr t -> Doc a -> Doc a
----exprCon2 expr doc = lhs <> rhs
----  where
----    lhs = parensIf useLeft (pretty expr)
----    rhs = if "" == show doc then "" else space <> doc
----    useLeft = case project expr of
----        ECon _ _ es | not (null es) -> True
----        ELam{}                      -> True
----        _                           -> False
--
----instance Pretty (SimplifiedExpr t) where
----
----    pretty = para $ \case
----        ECon    _ con []         -> pretty con
----        ECon    _ con es         -> pretty con <+> foldr exprCon2 "" (fst <$> es)
----        EApp    _ es             -> prettyApp (fst <$> es)
------        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
------        EFun    _ cs             -> "fun" <+> pipe -- <+> prettyClauses (fst <$$> cs)
----
------        EPat    _ [e] cs         -> "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)
----
----        expr -> snd <$> expr & \case
----
----            EVar    _ var        -> pretty var
----            ELit    _ prim       -> pretty prim
------            ELet    _ bind e1 e2 -> "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
----            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
----            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
----            _                    -> "TODO"
--
--instance Pretty (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))) where
--    pretty = para $ \case
--
--        ECon    _ con []         -> pretty con

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (ProgExpr t) where
    pretty = para $ \case
        ECon    _ con []         -> pretty con
        ECon    _ con es         -> pretty con <+> foldr exprCon "" (fst <$> es)
        EApp    _ es             -> prettyApp (fst <$> es)
--        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
--        EFun    _ cs             -> "fun" <+> pipe <+> prettyClauses (fst <$$> cs)
--        EPat    _ [e] cs         -> "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)

        expr -> snd <$> expr & \case

            EVar    _ var        -> pretty var
            ELit    _ prim       -> pretty prim
--            ELet    _ bind e1 e2 -> "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
--            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
--            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
            EOp1    _ (ONeg _) a -> "-" <> a
            EOp1    _ (ONot _) a -> "not" <+> a
            EOp2    _ op a b     -> a <+> pretty op <+> b
            ETuple  _ es         -> prettyTuple es
            EList   _ es         -> prettyList_ es
--            ERecord _ row        -> lbrace <+> prettyRow "=" row <+> rbrace

instance (Pretty b) => Pretty (Binding t b) where
    pretty = \case
        BLet _ pat  -> pretty pat
        BFun _ f ps -> pretty f <> prettyTuple (pretty <$> ps)

prettyApp :: (Pretty p) => [p] -> Doc a
prettyApp (f:args) = pretty f <> prettyTuple (pretty <$> args)

--instance (Pretty a) => Pretty (Clause t (ProgPattern t) a) where
--    pretty (Clause t ps gs) = pats <> guards
--      where
--        pats   | 1 == length ps = pretty (head ps)
--               | otherwise      = foldr patternCon "" ps 
--        guards | null gs        = ""
--               | otherwise      = commaSep (pretty <$> gs)
--
--instance (Pretty a) => Pretty (Guard a) where
--    pretty (Guard es e) = iffs <+> "=>" <+> pretty e
--      where
--        iffs | null es = ""
--             | otherwise = space <> "iff" <+> commaSep (pretty <$> es) 
--
--prettyClauses :: (Pretty p) => [p] -> Doc a
--prettyClauses cs = hsep (punctuate (space <> pipe) (pretty <$> cs))
--
--{-
--  match xs with
--    | Some y 
--      iff y > 10 => 1
--      iff y < 2  => 2
--      otherwise  => 3
---}

patternCon :: ProgPattern t -> Doc a -> Doc a
patternCon pat doc = lhs <> rhs
  where
    lhs = parensIf useLeft (pretty pat)
    rhs = if "" == show doc then "" else space <> doc
    useLeft = case project pat of
        PCon _ _ ps | not (null ps) -> True
        PAs{}                       -> True
        POr{}                       -> True
        _                           -> False

exprCon :: ProgExpr t -> Doc a -> Doc a
exprCon expr doc = lhs <> rhs
  where
    lhs = parensIf useLeft (pretty expr)
    rhs = if "" == show doc then "" else space <> doc
    useLeft = case project expr of
        ECon _ _ es | not (null es) -> True
        ELam{}                      -> True
        _                           -> False

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (Op1 t) where
    pretty = \case
        ONeg    _ -> "-"
        ONot    _ -> "not"

instance Pretty (Op2 t) where
    pretty = pretty . op2Symbol

---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--instance (Typed t, Pretty t) => Pretty (Ast t) where
--    pretty (Ast expr) = pretty (showTree tree)
--      where
--        tree = unpack . renderDoc <$> exprTree expr
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
--
----xxxExprTree :: (Typed t, Pretty t) => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> Tree (Doc a)
----xxxExprTree = para $ \case
----
----    EVar    t var        -> Node (annotated t var) []
----    ECon    t con es     -> Node (annotated t con) (snd <$> es)
----    ELit    t prim       -> Node (annotated t prim) []
----    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) 
----    EFix    t name e1 e2 -> Node "fix TODO" []
----    ELam    t ps e       -> Node (annotated t ("\\" <> ps)) [snd e]
----    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
----    EPat    t es cs      -> Node (xyz3 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
----    
----    _ -> Node "TODO" []
----
------xyz3 :: (Typed t, Pretty t, Pretty p) => p -> [(Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)), e)] -> Doc a
----xyz3 t es = "match" <+> commaSep (withTag3 . fst <$> es) <+> "with" <+> colon <+> pretty t
----
------withTag3 :: (Typed t, Pretty t) => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> Doc a
----withTag3 e = prettyFoo e -- annotated (typeOf (eTag e)) e 
------  where
------    eTag :: Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> t
------    eTag = cata $ \case
------        EVar    t _          -> t
------        ECon    t _ _        -> t
------        ELit    t prim       -> Node (annotated t prim) []
------        EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) 
------        EFix    t name e1 e2 -> Node "fix TODO" []
------        ELam    t ps e       -> Node "lam TODO" []
------        EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
------        EPat    t es cs      -> Node (xyz2 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
----
----prettyFoo = para $ \case
----        ECon    _ con []         -> pretty con
----        ECon    _ con es         -> pretty con <+> foldr exprCon2 "" (fst <$> es)
------        EApp    _ es             -> prettyApp (fst <$> es)
------        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
------        EFun    _ cs             -> "fun" <+> pipe -- <+> prettyClauses (fst <$$> cs)
----
------        EPat    _ [e] cs         -> "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)
----
----        expr -> snd <$> expr & \case
----
----            EVar    _ var        -> pretty var
------            ELit    _ prim       -> pretty prim
----            ELet    _ bind e1 e2 -> "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
----            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
----            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
--
--
--
----simplifiedExprTree :: (Typed t, Pretty t) => SimplifiedExpr t -> Tree (Doc a)
----simplifiedExprTree = para $ \case
----
----    EVar    t var        -> Node (annotated t var) []
----    ECon    t con es     -> Node (annotated t con) (snd <$> es)
----    ELit    t prim       -> Node (annotated t prim) []
----    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) 
----    EFix    t name e1 e2 -> Node "fix TODO" []
----    ELam    t ps e       -> Node (annotated t ("\\" <> ps)) [snd e]
----    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
----    EPat    t es cs      -> Node (xyz2 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
----
------ xyz :: (Typed t, Pretty p) => p -> [(ProgExpr t, e)] -> Doc a
----
----xyz2 :: (Typed t, Pretty t, Pretty p) => p -> [(SimplifiedExpr t, e)] -> Doc a
----xyz2 t es = "match" <+> commaSep (withTag2 . fst <$> es) <+> "with" <+> colon <+> pretty t
------xyz2 t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t
----
----withTag2 :: (Typed t, Pretty t) => SimplifiedExpr t -> Doc a
----withTag2 e = annotated (typeOf (eTag e)) e 
----  where
----    eTag :: SimplifiedExpr t -> t
----    eTag = cata $ \case
----        EVar    t _          -> t
----        ECon    t _ _        -> t
------        ELit    t prim       -> Node (annotated t prim) []
------        EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) 
------        EFix    t name e1 e2 -> Node "fix TODO" []
------        ELam    t ps e       -> Node "lam TODO" []
------        EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
------        EPat    t es cs      -> Node (xyz2 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

exprTree :: (Typed t, Pretty t) => ProgExpr t -> Tree (Doc a)
exprTree = para $ \case

    EVar    t var        -> Node (annotated t var) []
    ECon    t con es     -> Node (annotated t con) (snd <$> es)
    ELit    t prim       -> Node (annotated t prim) []
--    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) -- (annotated t (appExpr t (fst <$> es))) []
--    ELet    t bind e1 e2 -> letTree t bind (snd e1) (snd e2)
--    EFix    t name e1 e2 -> Node "fix TODO" []
--    ELam    t ps e       -> Node "lam TODO" []
--    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
--    EPat    t es cs      -> Node (xyz t es) (clauseTree <$> (fst <$$> cs))
--    EFun    t cs         -> Node (annotated t ("fun" :: Text)) (clauseTree <$> (fst <$$> cs))
--    EOp1    t (ONeg _) a -> op1Tree t ("negate" :: Text) (snd a)
--    EOp1    t (ONot _) a -> op1Tree t ("not" :: Text) (snd a)
--    EOp2    t op a b     -> op2Tree t op (snd a) (snd b)
--    ETuple  t es         -> Node (pretty t) (snd <$> es)
--    EList   t es         -> Node (pretty t) (snd <$> es)
--    ERecord t row        -> Node ("#Record" <+> pretty t) (foo <$> concatRowWithKey row)
--
--concatRowWithKey :: Row e -> [(Name, e)]
--concatRowWithKey (Row m _) = f =<< Map.foldrWithKey (curry (:)) mempty m
--  where 
--    f (n, es) = [(n, e) | e <- es]
--
--foo :: (Name, (ProgExpr t, Tree (Doc a))) -> Tree (Doc a)
--foo (a, b) = Node (pretty a) [snd b]
--
--xyz :: (Typed t, Pretty p) => p -> [(ProgExpr t, e)] -> Doc a
--xyz t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t

annotated :: (Pretty t, Pretty p) => t -> p -> Doc a
annotated t p = pretty p <+> colon <+> pretty t

--withTag :: (Typed t) => ProgExpr t -> Doc a
--withTag e = annotated (typeOf (exprTag e)) e 
--
--clauseTree :: (Typed t, Pretty t) => Clause t (ProgPattern t) (ProgExpr t) -> Tree (Doc a)
----clauseTree (Clause t ps gs) = Node (pats <+> colon <+> pretty t) (guard <$> gs) 
--clauseTree (Clause t ps gs) = Node pats (guard <$> gs)
--  where
--    pats | 1 == length ps = pretty (head ps) 
--         | otherwise      = foldr patternCon "" ps 
--    guard (Guard [] e)    = exprTree e
--    guard (Guard es e)    = Node (commaSep (iff <$> es)) [exprTree e]
--    iff e = "iff" <+> pretty e 
--
----op1Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a)
--op1Tree t op a = Node (annotated t op) [a]
--
----op2Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
--op2Tree t op a b = Node ("(" <> pretty op <> ")" <+> colon <+> pretty t) [a, b]
--
--letTree :: (Pretty t1, Pretty t2, Pretty p) => t1 -> Binding t2 p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
--letTree t bind e1 e2 =
--    Node (annotated t ("let" :: Text))
--        [ Node (annotated (bindingTag bind) bind <+> equals) [e1]
--        , Node "in" [e2]
--        ]
--
--ifTree :: (Pretty t) => t -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
--ifTree t e1 e2 e3 =
--    Node (annotated t ("if" :: Text))
--        [ e1 
--        , Node "then" [e2]
--        , Node "else" [e3]
--        ]
--
--instance Pretty (TypeInfoT [Error] Type) where
--    pretty (TypeInfo t ps es) = pretty t <> preds <> errs
--      where
--        preds | null ps   = ""
--              | otherwise = space <> pretty ps
--        errs  | null es   = ""
--              | otherwise = space <> pretty (parens . pretty <$$> es)
--
--instance (Show t) => Pretty (ErrorT t) where
--    pretty = pretty . show 
