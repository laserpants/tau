{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Pretty where

import Control.Arrow ((<<<), (>>>))
import Control.Monad ((<=<))
import Data.Function ((&))
import Data.List (null, intersperse)
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Data.Text (pack, unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
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
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
import qualified Tau.Compiler.Pipeline.Stage6 as Stage6


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

instance Pretty (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9) where
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
            PRow    _ ps     -> commaSep (prettyRow <$> ps)

prettyRow :: (Name, Doc a) -> Doc a
prettyRow (name, doc) = pretty name <+> equals <+> doc

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
    pretty ty 
        | isTupleType ty = prettyTupleType ty
        | otherwise      = prettyType ty

--        case leftmostTypeCon ty of
--            Just con | isTuple con -> prettyTupleType ty
--            Just "#Record"         -> prettyRecordType ty
--            _                      -> prettyType ty

prettyTupleType :: Type -> Doc a
prettyTupleType ty = let (_:ts) = unfoldApp ty in prettyTuple (pretty <$> ts)

--prettyRecordType :: Type -> Doc a
--prettyRecordType = project >>> \case
--    TApp (Fix (TCon _ "#Record")) row ->
--        lbrace <+> prettyRow ":" (pretty <$> typeToRow row) <+> rbrace

prettyType :: Type -> Doc a
prettyType = para $ \case

    TArr (t1, doc1) (_, doc2) ->
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
    TArr (a, _) (b, _)   -> [tArr a b]
    TCon kind con        -> [tCon kind con]
    TVar kind var        -> [tVar kind var]

--isTuple :: Name -> Bool
--isTuple con = Just True == (allCommas <$> stripped con)
--  where
--    allCommas = Text.all (== ',')
--    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("


--canonicalizeRowType :: Type -> Type
--canonicalizeRowType ty
--    | Just True == (isRowCon <$> leftmostTypeCon ty) = fromMap (toMap ty)
--    | otherwise = ty
--  where
--    isRowCon :: Name -> Bool
--    isRowCon con 
--      | Text.null con = False
--      | otherwise     = '{' == Text.head con && '}' == Text.last con
--
--    normalized = fromJust <<< Text.stripSuffix "}" <=< Text.stripPrefix "{"
--
--    toMap = para $ \case
--        TApp _ (Fix (TCon _ con), _) (b, (_, c)) -> (Map.singleton (normalized con) [b], c)
--        TApp _ (_, (a, _)) (_, (b, c))           -> (Map.unionWith (<>) a b, c)
--        TVar _ var                               -> (mempty, Just var)
--        TCon{}                                   -> mempty
--
--    fromMap (map, var) = 
--        Map.foldrWithKey (flip . foldr . tRowExtend) initl map
--      where
--        initl = case var of 
--            Nothing  -> tRowNil
--            Just var -> tVar kRow var


--yyy :: Type -> Map Name [Type]
--yyy (Fix (TApp _ a b)) = undefined
--yyy (Fix (TCon _ con)) = undefined


--  where
--    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("


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

instance (Pretty t, Pretty b) => Pretty (Binding t b) where
    pretty = \case
        BLet t pat  -> annotated t pat
        BFun _ f ps -> pretty f <> prettyTuple (pretty <$> ps)

instance (Pretty e1, Functor e3) => Pretty (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
    pretty = para $ \case
        ECon    _ con []         -> pretty con
        ECon    _ con es         -> pretty con <+> foldr exprCon "" (fst <$> es)
        EApp    _ es             -> prettyApp (fst <$> es)
        ELam    _ ps e           -> prettyLam ps (snd e) -- prettyTuple (pretty <$> ps) -- <+> "=>" <+> snd e
--        EFun    _ cs             -> "fun" <+> pipe <+> prettyClauses (fst <$$> cs)
        EPat    _ [e] cs         -> "TODO: pat" -- "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)

        expr -> snd <$> expr & \case

            EVar    _ var        -> pretty var
            ELit    _ prim       -> pretty prim
            ELet    _ bind e1 e2 -> prettyLet bind e1 e2 -- "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
--            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
--            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
            EOp1    _ (ONeg _) a -> "-" <> a
            EOp1    _ (ONot _) a -> "not" <+> a
            EOp2    _ op a b     -> a <+> pretty op <+> b
            ETuple  _ es         -> prettyTuple es
            EList   _ es         -> prettyList_ es
--            ERecord _ row        -> lbrace <+> prettyRow "=" row <+> rbrace
            _                    -> "!!TODO" 

prettyLam ps e = "TODO =>" <+> e

prettyLet :: (Pretty p) => p -> Doc a -> Doc a -> Doc a
prettyLet bind expr body =
    group (vsep
        [ nest 2 (vsep
            [ "let"
            , pretty bind <+> equals <+> expr
            , nest 2 (vsep ["in", body])
            ])
        ])

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

--patternCon :: ProgPattern t -> Doc a -> Doc a
--patternCon :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Doc a -> Doc a
--patternCon pat doc = lhs <> rhs
--  where
--    lhs = parensIf useLeft (pretty pat)
--    rhs = if "" == show doc then "" else space <> doc
--    useLeft = case project pat of
--        PCon _ _ ps | not (null ps) -> True
--        PAs{}                       -> True
--        POr{}                       -> True
--        _                           -> False

--exprCon :: (Functor clause) => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause -> Doc a -> Doc a
--exprCon expr doc = lhs <> rhs
--  where
--    lhs = parensIf useLeft (pretty expr)
--    rhs = if "" == show doc then "" else space <> doc
--    useLeft = case project expr of
--        ECon _ _ es | not (null es) -> True
--        ELam{}                      -> True
--        _                           -> False

patternCon
  :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
  -> Doc a
  -> Doc a
patternCon = prettyCon (project >>> \case
    PCon _ _ ps | not (null ps) -> True
    PAs{}                       -> True
    POr{}                       -> True
    _                           -> False)

exprCon
  :: (Pretty e1, Functor e3)
  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3
  -> Doc a
  -> Doc a
exprCon = prettyCon (project >>> \case
    ECon _ _ es | not (null es) -> True
    ELam{}                      -> True
    _                           -> False)

prettyCon :: (Pretty p) => (p -> Bool) -> p -> Doc a -> Doc a
prettyCon useParens expr doc = lhs <> rhs
  where
    lhs = parensIf (useParens expr) (pretty expr)
    rhs = if "" == show doc then "" else space <> doc

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
----bindingTypeInfoExprTree :: (Typed t, Pretty t) => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> Tree (Doc a)
----bindingTypeInfoExprTree = para $ \case
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
----withTag3 e = prettyLetBinding e -- annotated (typeOf (eTag e)) e
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
----prettyLetBinding = para $ \case
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

--exprTree :: (Typed t, Pretty t) => ProgExpr t -> Tree (Doc a)

class PatternClause c t p a where
    clauseLhs :: c t p a -> [p]
    clauseRhs :: c t p a -> [([a], a)]

instance PatternClause Clause t p (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
    clauseLhs = clausePatterns
    clauseRhs = (guardToPair <$>) . clauseGuards

instance PatternClause SimplifiedClause t p (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
    clauseLhs (SimplifiedClause _ ps _) = ps
    clauseRhs (SimplifiedClause _ _  g) = [guardToPair g]

exprTree
  :: (PatternClause c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, Typed t12, LetBinding e1, Pretty e1, Pretty e2, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t5, Pretty t6, Pretty t7, Pretty t8, Pretty t9, Pretty t10, Pretty t11, Pretty t12, Pretty t13, Pretty t15)
  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))
  -> Tree (Doc a)
exprTree = para $ \case

    EVar    t var        -> Node (annotated t var) []
    ECon    t con es     -> Node ("Con" <+> annotated t con) (snd <$> es)
    ELit    t prim       -> Node (annotated t prim) []
    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
    ELet    t bind e1 e2 -> Node (annotated t ("let" :: Text)) [Node (annotated (typeOf bind) (printLetBinding bind) <+> equals) [snd e1], Node "in" [snd e2]]
--    ELet    t bind e1 e2 -> Node (annotated t ("let" :: Text)) [Node (annotated (bindingTypeInfo bind) (printLetBinding bind) <+> equals) [snd e1], Node "in" [snd e2]]
    --EPat    t es cs      -> Node ("match" <+> commaSep (withTag . fst <$> es) <+> "with") (treeClause <$> (fst <$$> cs))
    --EPat    t [e] cs      -> Node ("match" <+> exprTree e <+> "with") (treeClause <$> (fst <$$> cs))

    EPat    t [e] cs     -> Node ("match" <+> colon <+> pretty t) ([exprTree (fst e)] <> [Node "with" (treeClause <$> (fst <$$> cs))])
    EFun    t cs         -> Node ("fun" <+> colon <+> pretty t) (treeClause <$> (fst <$$> cs))

    EOp1    _ op a       -> Node (pretty op) [snd a]
    --EOp2    _ op a b     -> Node ("(" <> pretty op  <> ")" <+> pretty (typeOf (op2Tag op))) [snd a, snd b]
    EOp2    _ op a b     -> Node (annotated (op2Tag op) (("(" <> op2Symbol op <> ")") :: Text)) [snd a, snd b]
--    ELam    t lam a      -> Node ("(" <> pretty lam <> ") =>") [snd a, Node (colon <+> "(" <> pretty t <> ")") []]
    ELam    t lam a      -> Node ("(" <> pretty lam <> ")" <+> "=>") [snd a] -- , Node (colon <+> "(" <> pretty t <> ")") []]
    ETuple  t es         -> Node (annotated t (tupleCon (length es))) (snd <$> es)
    EFix    t bind e1 e2 -> Node (annotated t ("fix" :: Text)) [Node (pretty bind <+> "=") [snd e1, Node "in" [snd e2]]]
    EIf     t e1 e2 e3   -> Node ("if" <+> colon <+> pretty t) [snd e1, prefix ("then" :: Text) (snd e2), prefix ("else" :: Text) (snd e3)]
    ERow    t es         -> Node (annotated t ("row" :: Text)) (foo <$> es)
    _                    -> Node "*TODO" []


foo :: (Name, (Expr t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 e0 e1 (c t (Pattern p0 p2 p3 p4 p5 p6 p7 p8 p9)), Tree (Doc a))) -> Tree (Doc a)
foo (a, (b, c)) = 
    Node (pretty a) [c]

prefix txt (Node label forest) = Node (pretty txt <+> label) forest

--exprTree3
--  :: (PatternClause c t (SimplifiedPattern t) (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t ())), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, Typed t12, LetBinding e1, Pretty e2, Pretty e1, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t5, Pretty t6, Pretty t7, Pretty t8, Pretty t9, Pretty t10, Pretty t11, Pretty t12, Pretty t13, Pretty t15)
--  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))
--  -> Tree (Doc a)
exprTree3 
  :: (Show t, Pretty t) => Stage6.SourceExpr t -> Tree (Doc a)
exprTree3 = para $ \case

    EVar    t var        -> Node (annotated t var) []
    ECon    t con es     -> Node ("Con" <+> annotated t con) (snd <$> es)
    ELit    t prim       -> Node (annotated t prim) []
    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
    EFix    t bind e1 e2 -> Node (annotated t ("fix" :: Text)) [Node (pretty bind <+> "=") [snd e1, Node "in" [snd e2]]]
    ELam    t lam a      -> Node ("(" <> pretty lam <> ") =>") [snd a] -- , Node (colon <+> "(" <> pretty t <> ")") []]
    EPat    t [e] cs     -> Node ("match" <+> colon <+> pretty t) ([exprTree3 (fst e)] <> [Node "with" (treeClause3 <$> (fst <$$> cs))])
    EIf     t e1 e2 e3   -> Node ("if" <+> colon <+> pretty t) [snd e1, prefix ("then" :: Text) (snd e2), prefix ("else" :: Text) (snd e3)]
    e                    -> Node (pretty (show e)) []


instance Pretty (SimplifiedPattern t) where
    pretty = \case
        SCon t con [] -> pretty con
        SCon t con rs -> pretty con <+> foldr patternConx "" rs -- (fst <$> rs)

--        PCon _ con ps -> pretty con <+> foldr patternCon "" (fst <$> ps)

--xx = Text.stripSuffix "]" <=< Text.stripPrefix "["
treeClause3 c = clauseTree3 (clauseLhs c) (clauseRhs c)

clauseTree3 :: (Pretty t, Show t) => [SimplifiedPattern t] -> [([Stage6.SourceExpr t], Stage6.SourceExpr t)] -> Tree (Doc a)
clauseTree3 ps gs = Node (pats <+> "=>") (guard <$> gs)
  where
    pats | 1 == length ps = pretty (head ps)
         | otherwise      = "xxxx" -- foldr patternConx "" ps
    guard ([], e) = exprTree3 e
    guard (es, e) = Node (commaSep (iff <$> es)) [exprTree3 e]
    iff e = "iff" <+> pretty e
--    guard ([], e)    = exprTree e
--    guard (es, e)    = Node (commaSep (iff <$> es)) [exprTree e]
--    iff e = "iff" <+> pretty e

patternConx :: Name -> Doc a -> Doc a
patternConx pat doc = pretty pat <+> doc
--patternCon :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Doc a -> Doc a
--patternCon pat doc = lhs <> rhs
--  where
--    lhs = parensIf useLeft (pretty pat)
--    rhs = if "" == show doc then "" else space <> doc
--    useLeft = case project pat of
--        PCon _ _ ps | not (null ps) -> True
--        PAs{}                       -> True
--        POr{}                       -> True
--        _                           -> False



--clauseTree ps gs = Node (pats <+> "=>") (guard <$> gs)
--  where
--    pats | 1 == length ps = pretty (head ps)
--         | otherwise      = foldr patternCon "" ps
--    guard ([], e)    = exprTree e
--    guard (es, e)    = Node (commaSep (iff <$> es)) [exprTree e]
--    iff e = "iff" <+> pretty e



treeClause 
  :: (Functor (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, Typed t22, LetBinding e1, Pretty e1, Pretty e2, Pretty t10, Pretty t12, Pretty t13, Pretty t14, Pretty t15, Pretty t16, Pretty t17, Pretty t18, Pretty t19, Pretty t20, Pretty t21, Pretty t22, Pretty t23, Pretty t25, PatternClause c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), PatternClause c2 t26 (Pattern t27 t28 t29 t30 t31 t32 t33 t34 t35) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)))) => c2 t26 (Pattern t27 t28 t29 t30 t31 t32 t33 t34 t35) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))) -> Data.Tree.Tree (Doc ann)
treeClause c = clauseTree (clauseLhs c) (clauseRhs c)

withTag
  :: (PatternClause c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, LetBinding e1, Pretty e1, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t7, Pretty t8, Pretty t9, Pretty t10, Pretty t11, Pretty t12)
  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))
  -> Doc a
withTag e = pretty e <+> colon <+> foo e -- (typeOf (exprTag e)) e
  where
--    foo :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)) -> Text
    foo = cata $ \case
        EVar    t _     -> pretty t
        ECon    t _ _   -> pretty t
        ELit    t _     -> pretty t
        EApp    t _     -> pretty t
        ELet    t _ _ _ -> pretty t
--        EFix    t _ _ _ -> pretty t
--        ELam    t _ _   -> pretty t
        EIf     t _ _ _ -> pretty t
        EPat    t _ _   -> pretty t
--        EFun    t _     -> pretty t
        EOp1    t _ _   -> pretty t
        EOp2    t _ _ _ -> pretty t
--        ETuple  t _     -> pretty t
--        EList   t _     -> pretty t
        _                -> "TODO"

--bindingTypeInfo
--  :: (Pretty bind)
--  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause
--  -> Guard (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause)
--bindingTypeInfo = undefined
--
--yyy
--  :: clause (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause)
--  -> Pattern u1 u2 u3 u4 u5 u6 u7 u8 u9
--yyy = undefined

--class C a where
--    xx :: a x -> Text
--    abc :: a x -> [p]
--    def :: a x -> [q]
--
--instance C (Clause t p) where
--    xx = undefined
--    abc (Clause t ps gs) = ps
--
----instance C (SimplifiedClause t p) where
----    xx = undefined

--clauseTree
--  :: (Typed bind, LetBinding bind, Functor clause, Pretty bind, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t8, Pretty t10)
--  => [Pattern u1 u2 u3 u4 u5 u6 u7 u8 u9]
--  -> [Guard (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause)]
--  -> Tree (Doc a)
clauseTree :: (PatternClause c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t11 t12 t13 t14 t15 t16 t17 t18 t19 t10 t20 t21 t22 t23 t24 bind lam (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed bind, Typed t21, LetBinding bind, Pretty bind, Pretty lam, Pretty t11, Pretty t12, Pretty t13, Pretty t14, Pretty t16, Pretty t18, Pretty t10, Pretty t15, Pretty t17, Pretty t19, Pretty t20, Pretty t21, Pretty t22, Pretty t24, Pretty a) => [Pattern t25 t26 t27 t28 t29 t30 t31 t32 t33] -> [([a], Expr t11 t12 t13 t14 t15 t16 t17 t18 t19 t10 t20 t21 t22 t23 t24 bind lam (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)))] -> Data.Tree.Tree (Doc ann)
clauseTree ps gs = Node (pats <+> "=>") (guard <$> gs)
  where
    pats | 1 == length ps = pretty (head ps)
         | otherwise      = foldr patternCon "" ps
    guard ([], e)    = exprTree e
    guard (es, e)    = Node (commaSep (iff <$> es)) [exprTree e]
    iff e = "iff" <+> pretty e

--clauseTree :: (C clause) => clause (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause) -> Tree (Doc a)
--clauseTree c = undefined
--  where
--    ps = abc c
--    gs = def c
--
--    pats | 1 == length ps = pretty (head ps)
--         | otherwise      = foldr patternCon "" ps
--    guard (Guard [] e)    = exprTree e
--    guard (Guard es e)    = Node (commaSep (iff <$> es)) [exprTree e]
--    iff e = "iff" <+> pretty e

--xyz :: (Pretty p, Pretty t8) => p -> [(Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause, e)] -> Doc a
xyz t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t

--withTag _ = ""

--clauseTree (Clause t ps gs) = Node pats (guard <$> gs)
--  where
--    pats | 1 == length ps = pretty (head ps)
--         | otherwise      = foldr patternCon "" ps
--    guard (Guard [] e)    = exprTree e
--    guard (Guard es e)    = Node (commaSep (iff <$> es)) [exprTree e]
--    iff e = "iff" <+> pretty e


--withTag :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause -> Doc a
--withTag e = annotated (typeOf (exprTag e)) e


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

class LetBinding b where
    printLetBinding :: b -> Text
    bindingTypeInfo :: b -> TypeInfo [Error]

--instance (Pretty b) => LetBinding (Binding (TypeInfoT [Error] Type) b) where
instance (Typed t, Pretty t, Pretty b) => LetBinding (Binding (TypeInfoT [Error] t) b) where
    printLetBinding = prettyPrint
    bindingTypeInfo (BLet t _)   = undefined -- (nodeType t)
    bindingTypeInfo (BFun t _ _) = undefined -- t

instance LetBinding (ProgBinding (Maybe Type)) where
    printLetBinding = prettyPrint
    bindingTypeInfo _ = undefined -- TypeInfo (tVar kTyp "a") [] []

--instance (Pretty b) => LetBinding (Binding (TypeInfoT [Error] (Maybe Type)) b) where
--    printLetBinding = prettyPrint
--    bindingTypeInfo (BLet t _)   = fmap fromJust t
--    bindingTypeInfo (BFun t _ _) = fmap fromJust t

instance LetBinding Void where
    printLetBinding = prettyPrint
    bindingTypeInfo _ = undefined -- TypeInfo (tVar kTyp "a") [] []

--letTree
--  :: (Pretty t, Typed b, LetBinding b)
--  => t
--  -> b
--  -> Tree (Doc a)
--  -> Tree (Doc a)
--  -> Tree (Doc a)
--letTree t bind e1 e2 =
--    Node (annotated t ("let" :: Text))
--        [ Node (annotated (bindingTypeInfo bind) (printLetBinding bind) <+> equals) [e1]
--        , Node "in" [e2] ]

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

instance (Pretty t) => Pretty (TypeInfoT [Error] t) where
    pretty (TypeInfo es t ps) = pretty t <> preds <> errs
      where
        preds | null ps   = ""
              | otherwise = space <> pretty ps
        errs  | null es   = ""
              | otherwise = space <> pretty (parens . pretty <$$> es)

-- TODO
instance (Show t) => Pretty (ErrorT t) where
    pretty = pretty . show
