{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}
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
import Data.Tuple.Extra
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Compiler.Substitute hiding (null)
import Tau.Compiler.Unify
import Tau.Core
import Tau.Lang
import Tau.Prog
import Tau.Util
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
--import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
--import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
--import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
--import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
--import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
--import qualified Tau.Compiler.Pipeline.Stage6 as Stage6

parensIf :: Bool -> Doc a -> Doc a
parensIf True doc = parens doc 
parensIf _    doc = doc 

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep

prettyList_ :: [Doc a] -> Doc a
prettyList_ = brackets . commaSep

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
        TSymbol  a -> pretty a

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Kind where
    pretty = para $ \case
        KArr (k1, doc1) (_, doc2) ->
            parensIf addLeft doc1 <+> "->" <+> doc2
          where
            addLeft =
                case project k1 of
                    KArr{} -> True
                    _      -> False

        KVar var -> pretty var
        KCon con -> pretty con

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Type where
    pretty = para $ \case
        TArr (t1, doc1) (_, doc2) ->
            parensIf addLeft doc1 <+> "->" <+> doc2
          where
            addLeft =
                case project t1 of
                    TArr{} -> True
                    _      -> False

        TApp _ (Fix (TCon _ "#"), _) (t2, _) -> 
            if null fields
                then maybe "{}" (\v -> "{" <+> pretty v <+> "}") final
                else "{" <+> commaSep fields <+> maybe "}" 
                    (\v -> "|" <+> pretty v <+> "}") final
          where
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
            parensIf addLeft doc1 <+> parensIf addRight doc2
          where
            addLeft = 
                case project t1 of
                    TArr{} -> True
                    _      -> False

            addRight =
                case project t2 of
                    TApp{} -> True
                    TArr{} -> True
                    TRow{} -> True
                    _      -> False

        TVar _ var -> pretty var
        TCon _ con -> pretty con

        TRow label (t1, doc1) (t2, doc2) ->
            "{" <> pretty label <> "}" <+> parensIf addLeft doc1 
                                       <+> parensIf addRight doc2
          where
            addLeft = 
                case project t1 of
                    TArr{} -> True
                    _      -> False

            addRight =
                case project t2 of
                    TCon _ "{}" -> False
                    TVar{}      -> False
                    _           -> True

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (PredicateT Name) where
    pretty (InClass n t) = pretty n <+> pretty t

instance Pretty Predicate where
    pretty (InClass n t) = pretty n <+> parensIf (useParens t) (pretty t)
      where
        useParens = project >>> \case
            TApp{} -> True
            TArr{} -> True
            _      -> False

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9) where
    pretty = para $ \case

        PCon _ "(::)" [hd, tl]           -> snd hd <+> "::" <+> snd tl
        PCon _ "#" [(r, _)]              -> prettyRecord r
        PCon _ con []                    -> pretty con
        PCon _ con ps                    -> pretty con <> prettyTuple (snd <$> ps)

        PRow _ lab (a, doc1) (b, doc2) -> 
            pretty ("{" <> lab <> "}") <+> parensIf (useParens a) doc1 
                                       <+> parensIf (useParens b) doc2
          where
            useParens = project >>> \case
                PAs{}        -> True
                POr{}        -> True
                PAnn{}       -> True
                _            -> False

        expr -> snd <$> expr & \case
            PVar    _ var                -> pretty var
            PLit    _ prim               -> pretty prim
            PAs     _ name p             -> p <+> "as" <+> pretty name
            POr     _ p q                -> p <+> "or" <+> q
            PAny    _                    -> "_"
            PTuple  _ ps                 -> prettyTuple ps
            PList   _ ps                 -> prettyList_ ps
            PAnn    t p                  -> p <+> ":" <+> pretty t

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

instance Pretty (SimplifiedPattern t) where
    pretty (SCon _ con []) = pretty con
    pretty (SCon _ con ps) = prettyTuple (pretty <$> ps)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance (Pretty e1, FunArgs e2, Functor e3, Clauses [e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 e1 e2 e3)]) => Pretty (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 e1 e2 e3) where
    pretty = para $ \case

        ECon _ "(::)" [hd, tl]           -> snd hd <+> "::" <+> snd tl
        ECon _ "#" [(r, _)]              -> prettyRecord r
        ECon _ con []                    -> pretty con
        ECon _ con ps                    -> pretty con <> prettyTuple (snd <$> ps)
        --EPat    _ e1 cs                  -> group (nest 2 (vsep ["match" <+> snd e1 <+> "with", clauses (fst <$$> cs)]))
        --EFun    _ cs                     -> group (nest 2 (vsep ["fun", clauses (fst <$$> cs)]))
        EPat    _ e1 cs                  -> nest 2 (vsep ["match" <+> snd e1 <+> "with", clauses (fst <$$> cs)])
        EFun    _ cs                     -> nest 2 (vsep ["fun", clauses (fst <$$> cs)])

        EApp _ ((e, doc1):es) -> 
            parensIf addLeft doc1 <> prettyArgs es
          where
            prettyArgs [(Fix (ELit _ TUnit), _)] = "()"
            prettyArgs args = parens (commaSep (snd <$> args))

            addLeft = 
                case project e of
                    EVar{} -> False
                    _      -> True

        ERow _ lab (a, doc1) (b, doc2) -> 
            pretty ("{" <> lab <> "}") <+> parensIf (useParens a) doc1 
                                       <+> parensIf (useParens b) doc2
          where
            useParens = project >>> \case
                EOp2{}       -> True
                EIf{}        -> True
                EAnn{}       -> True
                ERow{}       -> True
                _            -> False

        ELet _ bind e1 e2 -> 
            prettyLet (pretty bind) (rhs e1) (snd e2)

          where
            --
            --  :: (Functor e3, Clauses [e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3)]) 
            --  => (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3, Doc a) 
            --  -> Doc a
            rhs (expr, doc) = 
                case project expr of
                    EFun _ cs -> line' <> clauses cs
                    _         -> group (vsep ["=", doc])



        ELam _ ps e                      -> prettyLam (funArgs ps) (snd e)

        expr -> snd <$> expr & \case
            EVar    _ var                -> pretty var
            EHole   _                    -> "_"
            ELit    _ prim               -> pretty prim
            EIf     _ e1 e2 e3           -> prettyIf e1 e2 e3
            EFix    _ name e1 e2         -> prettyFix name e1 e2
            EOp1    _ op a               -> pretty op <> a
            EOp2    _ (ODot _) a b       -> b <> "." <> a
            EOp2    _ (OField _) a b     -> b <> "." <> a
            EOp2    _ op a b             -> a <+> pretty op <+> b
            ETuple  _ es                 -> prettyTuple es
            EList   _ es                 -> prettyList_ es
            EAnn    t e                  -> e <+> ":" <+> pretty t

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

prettyLet 
  :: Doc a 
  -> Doc a
  -> Doc a 
  -> Doc a
prettyLet bind e1 e2 =
    group (nest 2 (vsep
        [ "let" <+> bind <+> e1
        , nest 2 (vsep ["in", e2])
        ]))

prettyLam :: Doc a -> Doc a -> Doc a 
prettyLam args body = group (nest 2 (vsep [args <+> "=>", body]))

prettyIf :: Doc a -> Doc a -> Doc a -> Doc a 
prettyIf e1 e2 e3 =
    "if" <> softline <> e1 <> space <> group (nest 2 (line' <> vsep 
        [ group (nest 2 (vsep ["then", e2]))
        , group (nest 2 (vsep ["else", e3]))
        ]))

--prettyLet 
--  :: (Functor e3, Clauses [e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3)]) 
--  => Doc a 
--  -> (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3, Doc a) 
--  -> Doc a 
--  -> Doc a
--prettyLet bind e1 e2 = 
--    group (nest 2 (vsep
--        [ "let" <+> bind <+> body
--        , nest 2 (vsep ["in", e2])
--        ]))
--  where 
--    body = case project (fst e1) of
--        EFun _ cs -> line' <> clauses cs
--        _         -> group (vsep ["=", snd e1])

prettyFix :: Pretty p => p -> Doc a -> Doc a -> Doc a
prettyFix name e1 e2 =
    group (nest 2 (vsep
        [ "fix" <+> pretty name <+> "="
        , e1
        , nest 2 (vsep ["in", e2])
        ]))

--prettyLet 
--  :: (Functor e3, Pretty p, Clauses [e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3)]) 
--  => p 
--  -> (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3, Doc a) 
--  -> Doc a 
--  -> Doc a
--prettyLet bind e1 e2 = "let" <+> pretty bind <+> body <+> "in" <+> e2 where 
--    body = case project (fst e1) of
--        EFun _ cs -> clauses cs
--        _         -> "=" <+> snd e1

--instance Pretty (Binding t (ProgPattern t)) where
--    pretty = \case
--        BPat _ p    -> pretty p
--        BFun _ f ps -> pretty f <> prettyArgs ps
--          where
--            prettyArgs [Fix (PLit _ TUnit)] = "()"
--            prettyArgs args = parens (commaSep (pretty <$> args))

instance Pretty (Op1 t) where
    pretty = \case
        ONeg    _ -> "-"
        ONot    _ -> "not"

instance Pretty (Op2 t) where
    pretty = pretty . op2Symbol

instance Pretty (Binding t (Pattern t t t s s t s s s)) where
    pretty = \case
        BPat _ p    -> pretty p
        BFun _ f ps -> pretty f <> prettyArgs ps
          where
            prettyArgs [Fix (PLit _ TUnit)] = "()"
            prettyArgs args = parens (commaSep (pretty <$> args))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

class FunArgs f where
    funArgs :: f -> Doc a

instance FunArgs Text where
    funArgs = pretty

instance FunArgs [(ProgPattern t, Doc a)] where
    funArgs ps = funArgs (fst <$> ps)

instance FunArgs [(ProgPattern t)] where
    funArgs [p] = parensIf (useParens p) (pretty p)
      where
        useParens = project >>> \case
            PVar{} -> False
            PLit{} -> False
            _      -> True

    funArgs ps  = "(" <> commaSep (pretty <$> ps) <> ")"

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

class Clauses c where
    clauses :: c -> Doc a

instance (Pretty p, Pretty a) => Clauses [SimplifiedClause t p a] where
    clauses = hsep . fmap pretty

instance (Pretty p, Pretty a) => Pretty (SimplifiedClause t p a) where
    pretty (SimplifiedClause _ p g) = pipe <+> pretty p <+> prettyGuard g

instance (Pretty p, Pretty a, Width p, Width a) => Clauses [Clause t p a] where
    --clauses cs = group (vsep (prettyClause <$> cs))
    clauses cs = vsep (prettyClause <$> cs)
      where
        --prettyClause (Clause _ p gs) = pipe <+> fillBreak maxW (pretty p) <+> prettyGuard gs
        prettyClause (Clause _ p gs) = pipe <+> fill maxW (pretty p) <+> prettyGuard gs

        -- TODO
        prettyGuard []           = ""
        prettyGuard [Guard [] e] = "=>" <+> pretty e
        prettyGuard gs           = nest 4 (line' <> vsep (prettyG <$> gs))

        -- TODO
        prettyG (Guard es e) = fill (maxW - 2) (prettyIffs es) <+> "=>" <+> pretty e 

        maxW = maximum (widthOf <$> cs)

        fill n a = flatAlt (fillBreak n a) a
        --fill n a = group (flatAlt (fillBreak n a) a)

class Width a where
    widthOf :: a -> Int

layoutWidth :: Doc a -> Int
--layoutWidth d = n where (SText n _ _) = layoutPretty defaultLayoutOptions d
layoutWidth = length . show

instance (Pretty a, Width a, Width p) => Width (Clause t p a) where
    widthOf (Clause _ p gs) = maximum (widthOf p:fmap ((+2) . widthOf) gs)

instance Width (ProgExpr t) where
    widthOf = layoutWidth . pretty

instance Width (ProgPattern t) where
    widthOf = layoutWidth . pretty

instance Width [ProgPattern t] where
    widthOf _ = 10 -- TODO TODO TODO TODO TODO

instance (Pretty a, Width a) => Width (Guard a) where
    widthOf (Guard [] _) = 0
    widthOf (Guard es _) = layoutWidth (prettyIffs es)

instance (Pretty p, Pretty a) => Pretty (Clause t p a) where
    pretty (Clause _ p gs) = pipe <+> pretty p <+> prettyGuard gs

instance (Pretty a) => Pretty (Guard a) where
    pretty (Guard es e) = prettyIffs es <> "=>" <+> pretty e 

prettyIffs :: (Pretty p) => [p] -> Doc a
prettyIffs = \case 
    [] -> "otherwise" -- space??
    es -> "when" <> prettyTuple (pretty <$> es) 

--instance (Pretty a) => Pretty (Guard a) where
--    pretty (Guard es e) = iffs <> "=>" <+> pretty e 
--      where
--        iffs = case es of
--            [] -> "otherwise "
--            _  -> hsep (prettyIff <$> es) <> " "
--
--        prettyIff e = "iff" <> parens (pretty e)

class Guarded g where
    prettyGuard :: g -> Doc a

instance (Pretty a) => Guarded [Guard a] where
    prettyGuard []           = ""
    prettyGuard [Guard [] e] = "=>" <+> pretty e
    prettyGuard gs           = nest 4 (line' <> vsep (pretty <$> gs))

instance (Pretty a) => Guarded (Guard a) where
    prettyGuard = pretty 

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Error where
    pretty = \case 
        CannotUnify t1 t2 err -> ("CannotUnify '" <> pretty t1 <> "' with '" <> pretty t2 <> "' " <> pretty err)
        -- TODO
        e -> pretty (show e)

instance Pretty UnificationError where
    pretty = \case 
        -- TODO
        e -> pretty (show e)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

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

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

instance Pretty Core where
    pretty = para $ \case

        CApp ((e, doc1):es) ->
            parensIf addLeft doc1 <> prettyArgs es
          where
            --prettyArgs [(Fix (ELit _ TUnit), _)] = "()"
            prettyArgs args = parens (commaSep (snd <$> args))

            addLeft = 
                case project e of
                    CVar{} -> False
                    _      -> True

        expr -> snd <$> expr & \case

            CVar var                     -> pretty var
            CLit prim                    -> pretty prim
            CLet name e1 e2              -> prettyLet (pretty name <+> "=") e1 e2
            CLam name e1                 -> prettyLam (pretty name) e1 
            CIf  e1 e2 e3                -> prettyIf e1 e2 e3
            CPat e1 cs                   -> nest 2 (vsep ["match" <+> e1 <+> "with", coreClauses cs])

coreClauses cs = vsep (prettyClause <$> cs)
  where
    prettyClause (ns, e) = pipe <+> prettyTuple (pretty <$> ns) <+> "=>" <+> e





--
----instance (Eq e, Pretty e) => Pretty (Row e) where
----    pretty (Row map r) | null map = maybe "{}" pretty r
----    pretty row = lbrace <+> prettyRow ":" (pretty <$> row) <+> rbrace
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----instance (Pretty t, Pretty b) => Pretty (Binding t b) where
----    pretty = \case
----        BPat t pat  -> annotated t pat
----        BFun _ f ps -> pretty f <> prettyTuple (pretty <$> ps)
--
--
----instance Pretty (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9) where
----    pretty = para $ \case
----
----        PCon _ con [] -> pretty con
----        PCon _ con ps -> pretty con <+> foldr patternCon "" (fst <$> ps)
----
----        expr -> snd <$> expr & \case
----            PVar    _ var    -> pretty var
----            PLit    _ prim   -> pretty prim
----            PAs     _ name p -> p <+> "as" <+> pretty name
----            POr     _ p q    -> p <+> "or" <+> q
----            PAny    _        -> "_"
----            PTuple  _ ps     -> prettyTuple ps
----            PList   _ ps     -> prettyList_ ps
----            PRow    _ l p q  -> "..."
----
----prettyRow :: (Name, Doc a) -> Doc a
----prettyRow (name, doc) = pretty name <+> equals <+> doc
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----       case leftmostTypeCon ty of
----           Just con | isTuple con -> prettyTupleType ty
----           Just "#Record"         -> prettyRecordType ty
----           _                      -> prettyType ty
--
----instance Pretty Type where
----    pretty ty
----       | isTupleType ty = prettyTupleType ty
----       | otherwise      = prettyType ty
----      where
----        isTupleType ty  = Just True == maybeIsTupleCon
----        maybeIsTupleCon = Text.all (== ',') <$> (stripped <=< leftmost) ty
----        stripped        = Text.stripSuffix ")" <=< Text.stripPrefix "("
----
----        leftmost :: Type -> Maybe Name
----        leftmost = cata $ \case
----            TCon _ con   -> Just con
----            TApp _ a _   -> a
----            _            -> Nothing
----
----prettyTupleType :: Type -> Doc a
----prettyTupleType ty = let (_:ts) = unfoldApp ty in prettyTuple (pretty <$> ts)
--
----prettyRecordType :: Type -> Doc a
----prettyRecordType = project >>> \case
----    TApp (Fix (TCon _ "#Record")) row ->
----        lbrace <+> prettyRow ":" (pretty <$> typeToRow row) <+> rbrace
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----instance Pretty Scheme where
----    pretty _ = "TODO"
----
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
----
----instance (Pretty t) => Pretty (Substitution t) where
----    pretty _ = "TODO"
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----prettyRow :: Doc a -> Row (Doc a) -> Doc a
----prettyRow delim row@(Row map r) = body <> leaf
----  where
----    leaf = case r of
----        Nothing -> ""
----        Just q  -> " " <> pipe <+> q
----
----    body = case rowDoc row of
----        RNil     -> "{}"
----        RVar var -> var
----        RExt     -> fields (elm <$> Map.toList map)
----
----    elm (k, es) = fields ((\y -> pretty k <+> delim <+> y) <$> es)
----    fields f    = mconcat (intersperse ", " f)
----
----rowDoc :: Row (Doc a) -> RowType (Doc a)
----rowDoc (Row m Nothing)  | null m = RNil
----rowDoc (Row m (Just r)) | null m = RVar r
----rowDoc _                         = RExt
--
----isTuple :: Name -> Bool
----isTuple con = Just True == (allCommas <$> stripped con)
----  where
----    allCommas = Text.all (== ',')
----    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("
--
--
----canonicalizeRowType :: Type -> Type
----canonicalizeRowType ty
----    | Just True == (isRowCon <$> leftmostTypeCon ty) = fromMap (toMap ty)
----    | otherwise = ty
----  where
----    isRowCon :: Name -> Bool
----    isRowCon con 
----      | Text.null con = False
----      | otherwise     = '{' == Text.head con && '}' == Text.last con
----
----    normalized = fromJust <<< Text.stripSuffix "}" <=< Text.stripPrefix "{"
----
----    toMap = para $ \case
----        TApp _ (Fix (TCon _ con), _) (b, (_, c)) -> (Map.singleton (normalized con) [b], c)
----        TApp _ (_, (a, _)) (_, (b, c))           -> (Map.unionWith (<>) a b, c)
----        TVar _ var                               -> (mempty, Just var)
----        TCon{}                                   -> mempty
----
----    fromMap (map, var) = 
----        Map.foldrWithKey (flip . foldr . tRowExtend) initl map
----      where
----        initl = case var of 
----            Nothing  -> tRowNil
----            Just var -> tVar kRow var
--
--
----yyy :: Type -> Map Name [Type]
----yyy (Fix (TApp _ a b)) = undefined
----yyy (Fix (TCon _ con)) = undefined
--
--
----  where
----    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("
--
--
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
----
------exprCon2 :: SimplifiedExpr t -> Doc a -> Doc a
------exprCon2 expr doc = lhs <> rhs
------  where
------    lhs = parensIf addLeft (pretty expr)
------    rhs = if "" == show doc then "" else space <> doc
------    addLeft = case project expr of
------        ECon _ _ es | not (null es) -> True
------        ELam{}                      -> True
------        _                           -> False
----
------instance Pretty (SimplifiedExpr t) where
------
------    pretty = para $ \case
------        ECon    _ con []         -> pretty con
------        ECon    _ con es         -> pretty con <+> foldr exprCon2 "" (fst <$> es)
------        EApp    _ es             -> prettyApp (fst <$> es)
--------        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
--------        EFun    _ cs             -> "fun" <+> pipe -- <+> prettyClauses (fst <$$> cs)
------
--------        EPat    _ [e] cs         -> "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)
------
------        expr -> snd <$> expr & \case
------
------            EVar    _ var        -> pretty var
------            ELit    _ prim       -> pretty prim
--------            ELet    _ bind e1 e2 -> "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
------            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
------            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
------            _                    -> "TODO"
----
----instance Pretty (Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t))) where
----    pretty = para $ \case
----
----        ECon    _ con []         -> pretty con
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----instance (Pretty e1, Functor e3) => Pretty (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
----    pretty = para $ \case
----        ECon    _ con []         -> pretty con
----        ECon    _ con es         -> pretty con <+> foldr exprCon "" (fst <$> es)
----        EApp    _ es             -> prettyApp (fst <$> es)
----        ELam    _ ps e           -> prettyLam ps (snd e) -- prettyTuple (pretty <$> ps) -- <+> "=>" <+> snd e
------        EFun    _ cs             -> "fun" <+> pipe <+> prettyClauses (fst <$$> cs)
----        EPat    _ e cs           -> "TODO: pat" -- "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)
----
----        expr -> snd <$> expr & \case
----
----            EVar    _ var        -> pretty var
----            ELit    _ prim       -> pretty prim
----            ELet    _ bind e1 e2 -> prettyLet bind e1 e2 -- "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
------            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
------            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
----            EOp1    _ (ONeg _) a -> "-" <> a
----            EOp1    _ (ONot _) a -> "not" <+> a
----            EOp2    _ op a b     -> a <+> pretty op <+> b
----            ETuple  _ es         -> prettyTuple es
----            EList   _ es         -> prettyList_ es
------            ERecord _ row        -> lbrace <+> prettyRow "=" row <+> rbrace
----            _                    -> "!!TODO" 
--
--prettyLam ps e = "TODO =>" <+> e
--
--prettyApp :: (Pretty p) => [p] -> Doc a
--prettyApp (f:args) = pretty f <> prettyTuple (pretty <$> args)
--
----instance (Pretty a) => Pretty (Clause t (ProgPattern t) a) where
----    pretty (Clause t ps gs) = pats <> guards
----      where
----        pats   | 1 == length ps = pretty (head ps)
----               | otherwise      = foldr patternCon "" ps
----        guards | null gs        = ""
----               | otherwise      = commaSep (pretty <$> gs)
----
----instance (Pretty a) => Pretty (Guard a) where
----    pretty (Guard es e) = iffs <+> "=>" <+> pretty e
----      where
----        iffs | null es = ""
----             | otherwise = space <> "iff" <+> commaSep (pretty <$> es)
----
----prettyClauses :: (Pretty p) => [p] -> Doc a
----prettyClauses cs = hsep (punctuate (space <> pipe) (pretty <$> cs))
----
----{-
----  match xs with
----    | Some y
----      iff y > 10 => 1
----      iff y < 2  => 2
----      otherwise  => 3
-----}
--
----patternCon :: ProgPattern t -> Doc a -> Doc a
----patternCon :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Doc a -> Doc a
----patternCon pat doc = lhs <> rhs
----  where
----    lhs = parensIf addLeft (pretty pat)
----    rhs = if "" == show doc then "" else space <> doc
----    addLeft = case project pat of
----        PCon _ _ ps | not (null ps) -> True
----        PAs{}                       -> True
----        POr{}                       -> True
----        _                           -> False
--
----exprCon :: (Functor clause) => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause -> Doc a -> Doc a
----exprCon expr doc = lhs <> rhs
----  where
----    lhs = parensIf addLeft (pretty expr)
----    rhs = if "" == show doc then "" else space <> doc
----    addLeft = case project expr of
----        ECon _ _ es | not (null es) -> True
----        ELam{}                      -> True
----        _                           -> False
--
--patternCon
--  :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9
--  -> Doc a
--  -> Doc a
--patternCon = prettyCon (project >>> \case
--    PCon _ _ ps | not (null ps) -> True
--    PAs{}                       -> True
--    POr{}                       -> True
--    _                           -> False)
--
--exprCon
--  :: (FunArgs e2, Pretty e1, Pretty e2, Functor e3)
--  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3
--  -> Doc a
--  -> Doc a
--exprCon = undefined -- prettyCon (project >>> \case
----    ECon _ _ es | not (null es) -> True
----    ELam{}                      -> True
----    _                           -> False)
--
--prettyCon :: (Pretty p) => (p -> Bool) -> p -> Doc a -> Doc a
--prettyCon useParens expr doc = lhs <> rhs
--  where
--    lhs = parensIf (useParens expr) (pretty expr)
--    rhs = if "" == show doc then "" else space <> doc
--
---- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----instance Pretty (Op1 t) where
----    pretty = \case
----        ONeg    _ -> "-"
----        ONot    _ -> "not"
----
----instance Pretty (Op2 t) where
----    pretty = pretty . op2Symbol
--
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
----
----instance (Typed t, Pretty t) => Pretty (Ast t) where
----    pretty (Ast expr) = pretty (showTree tree)
----      where
----        tree = unpack . renderDoc <$> exprTree expr
----
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
----
----
------bindingTypeInfoExprTree :: (Typed t, Pretty t) => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> Tree (Doc a)
------bindingTypeInfoExprTree = para $ \case
------
------    EVar    t var        -> Node (annotated t var) []
------    ECon    t con es     -> Node (annotated t con) (snd <$> es)
------    ELit    t prim       -> Node (annotated t prim) []
------    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
------    EFix    t name e1 e2 -> Node "fix TODO" []
------    ELam    t ps e       -> Node (annotated t ("\\" <> ps)) [snd e]
------    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
------    EPat    t es cs      -> Node (xyz3 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
------
------    _ -> Node "TODO" []
------
--------xyz3 :: (Typed t, Pretty t, Pretty p) => p -> [(Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)), e)] -> Doc a
------xyz3 t es = "match" <+> commaSep (withTag3 . fst <$> es) <+> "with" <+> colon <+> pretty t
------
--------withTag3 :: (Typed t, Pretty t) => Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> Doc a
------withTag3 e = prettyLetBinding e -- annotated (typeOf (eTag e)) e
--------  where
--------    eTag :: Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> t
--------    eTag = cata $ \case
--------        EVar    t _          -> t
--------        ECon    t _ _        -> t
--------        ELit    t prim       -> Node (annotated t prim) []
--------        EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
--------        EFix    t name e1 e2 -> Node "fix TODO" []
--------        ELam    t ps e       -> Node "lam TODO" []
--------        EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
--------        EPat    t es cs      -> Node (xyz2 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
------
------prettyLetBinding = para $ \case
------        ECon    _ con []         -> pretty con
------        ECon    _ con es         -> pretty con <+> foldr exprCon2 "" (fst <$> es)
--------        EApp    _ es             -> prettyApp (fst <$> es)
--------        ELam    _ ps e           -> prettyTuple (pretty <$> ps) <+> "=>" <+> snd e
--------        EFun    _ cs             -> "fun" <+> pipe -- <+> prettyClauses (fst <$$> cs)
------
--------        EPat    _ [e] cs         -> "match" <+> snd e <+> "with" <+> prettyClauses (fst <$$> cs)
------
------        expr -> snd <$> expr & \case
------
------            EVar    _ var        -> pretty var
--------            ELit    _ prim       -> pretty prim
------            ELet    _ bind e1 e2 -> "let" <+> pretty bind <+> equals <+> e1 <+> "in" <+> e2
------            EFix    _ name e1 e2 -> "fix" <+> pretty name <+> equals <+> e1 <+> "in" <+> e2
------            EIf     _ e1 e2 e3   -> "if" <+> e1 <+> "then" <+> e2 <+> "else" <+> e3
----
----
----
------simplifiedExprTree :: (Typed t, Pretty t) => SimplifiedExpr t -> Tree (Doc a)
------simplifiedExprTree = para $ \case
------
------    EVar    t var        -> Node (annotated t var) []
------    ECon    t con es     -> Node (annotated t con) (snd <$> es)
------    ELit    t prim       -> Node (annotated t prim) []
------    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
------    EFix    t name e1 e2 -> Node "fix TODO" []
------    ELam    t ps e       -> Node (annotated t ("\\" <> ps)) [snd e]
------    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
------    EPat    t es cs      -> Node (xyz2 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
------
-------- xyz :: (Typed t, Pretty p) => p -> [(ProgExpr t, e)] -> Doc a
------
------xyz2 :: (Typed t, Pretty t, Pretty p) => p -> [(SimplifiedExpr t, e)] -> Doc a
------xyz2 t es = "match" <+> commaSep (withTag2 . fst <$> es) <+> "with" <+> colon <+> pretty t
--------xyz2 t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t
------
------withTag2 :: (Typed t, Pretty t) => SimplifiedExpr t -> Doc a
------withTag2 e = annotated (typeOf (eTag e)) e
------  where
------    eTag :: SimplifiedExpr t -> t
------    eTag = cata $ \case
------        EVar    t _          -> t
------        ECon    t _ _        -> t
--------        ELit    t prim       -> Node (annotated t prim) []
--------        EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
--------        EFix    t name e1 e2 -> Node "fix TODO" []
--------        ELam    t ps e       -> Node "lam TODO" []
--------        EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
--------        EPat    t es cs      -> Node (xyz2 t es) undefined -- (xyz t es) (clauseTree <$> (fst <$$> cs))
----
------ >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
--
----exprTree :: (Typed t, Pretty t) => ProgExpr t -> Tree (Doc a)
--
--class PatternClause c t p a where
--    clauseLhs :: c t p a -> [p]
--    clauseRhs :: c t p a -> [([a], a)]
--
--instance PatternClause Clause t p (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
--    clauseLhs xx = let zz = clausePatterns xx in [zz]
--    clauseRhs = (guardToPair <$>) . clauseGuards
--
--instance PatternClause SimplifiedClause t p (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
--    clauseLhs (SimplifiedClause _ ps _) = ps
--    clauseRhs (SimplifiedClause _ _  g) = [guardToPair g]
--
--exprTree
--  :: (FunArgs e2, PatternClause c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, Typed t12, LetBinding e1, Pretty e1, Pretty e2, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t5, Pretty t6, Pretty t7, Pretty t8, Pretty t9, Pretty t10, Pretty t11, Pretty t12, Pretty t13, Pretty t15)
--  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))
--  -> Tree (Doc a)
--exprTree = para $ \case
--
--    EVar    t var        -> Node (annotated t var) []
--    ECon    t con es     -> Node ("Con" <+> annotated t con) (snd <$> es)
--    ELit    t prim       -> Node (annotated t prim) []
--    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
--    ELet    t bind e1 e2 -> Node (annotated t ("let" :: Text)) [Node (annotated (typeOf bind) (printLetBinding bind) <+> equals) [snd e1], Node "in" [snd e2]]
----    ELet    t bind e1 e2 -> Node (annotated t ("let" :: Text)) [Node (annotated (bindingTypeInfo bind) (printLetBinding bind) <+> equals) [snd e1], Node "in" [snd e2]]
--    --EPat    t es cs      -> Node ("match" <+> commaSep (withTag . fst <$> es) <+> "with") (treeClause <$> (fst <$$> cs))
--    --EPat    t [e] cs      -> Node ("match" <+> exprTree e <+> "with") (treeClause <$> (fst <$$> cs))
--
--    EPat    t e cs       -> Node "TODO123" [] -- Node ("match" <+> colon <+> pretty t) ([exprTree (fst e)] <> [Node "with" (treeClause <$> (fst <$$> cs))])
--    EFun    t cs         -> undefined -- Node ("fun" <+> colon <+> pretty t) (treeClause <$> (fst <$$> cs))
--
--    EOp1    _ op a       -> Node (pretty op) [snd a]
--    --EOp2    _ op a b     -> Node ("(" <> pretty op  <> ")" <+> pretty (typeOf (op2Tag op))) [snd a, snd b]
--    EOp2    _ op a b     -> Node (annotated (op2Tag op) (("(" <> op2Symbol op <> ")") :: Text)) [snd a, snd b]
----    ELam    t lam a      -> Node ("(" <> pretty lam <> ") =>") [snd a, Node (colon <+> "(" <> pretty t <> ")") []]
--    ELam    t lam a      -> Node ("(" <> pretty lam <> ")" <+> "=>") [snd a] -- , Node (colon <+> "(" <> pretty t <> ")") []]
--    ETuple  t es         -> Node (annotated t (tupleCon (length es))) (snd <$> es)
--    EFix    t bind e1 e2 -> Node (annotated t ("fix" :: Text)) [Node (pretty bind <+> "=") [snd e1, Node "in" [snd e2]]]
--    EIf     t e1 e2 e3   -> Node ("if" <+> colon <+> pretty t) [snd e1, prefix ("then" :: Text) (snd e2), prefix ("else" :: Text) (snd e3)]
--    ERow    t l a b      -> Node "<row>" [Node (pretty l) [snd a], snd b] -- Node (annotated t ("row" :: Text)) (foo <$> es)
--    _                    -> Node "*TODO" []
--
--
--
--foo :: (Name, (Expr t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 e0 e1 (c t (Pattern p0 p2 p3 p4 p5 p6 p7 p8 p9)), Tree (Doc a))) -> Tree (Doc a)
--foo (a, (b, c)) = 
--    Node (pretty a) [c]
--
--prefix txt (Node label forest) = Node (pretty txt <+> label) forest
--
----exprTree3
----  :: (PatternClause c t (SimplifiedPattern t) (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t ())), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, Typed t12, LetBinding e1, Pretty e2, Pretty e1, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t5, Pretty t6, Pretty t7, Pretty t8, Pretty t9, Pretty t10, Pretty t11, Pretty t12, Pretty t13, Pretty t15)
----  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))
----  -> Tree (Doc a)
--exprTree3 
--  :: (Show t, Pretty t) => Stage6.SourceExpr t -> Tree (Doc a)
--exprTree3 = para $ \case
--
--    EVar    t var        -> Node (annotated t var) []
--    ECon    t con es     -> Node ("Con" <+> annotated t con) (snd <$> es)
--    ELit    t prim       -> Node (annotated t prim) []
--    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es)
--    EFix    t bind e1 e2 -> Node (annotated t ("fix" :: Text)) [Node (pretty bind <+> "=") [snd e1, Node "in" [snd e2]]]
--    ELam    t lam a      -> Node ("(" <> pretty lam <> ") =>") [snd a] -- , Node (colon <+> "(" <> pretty t <> ")") []]
--    EPat    t e cs       -> Node "TODO456" [] -- Node ("match" <+> colon <+> pretty t) ([exprTree3 (fst e)] <> [Node "with" (treeClause3 <$> (fst <$$> cs))])
--    EIf     t e1 e2 e3   -> Node ("if" <+> colon <+> pretty t) [snd e1, prefix ("then" :: Text) (snd e2), prefix ("else" :: Text) (snd e3)]
--    e                    -> Node (pretty (show e)) []
--
--
--instance Pretty (SimplifiedPattern t) where
--    pretty = \case
--        SCon t con [] -> pretty con
--        SCon t con rs -> pretty con <+> foldr patternConx "" rs -- (fst <$> rs)
--
----        PCon _ con ps -> pretty con <+> foldr patternCon "" (fst <$> ps)
--
----xx = Text.stripSuffix "]" <=< Text.stripPrefix "["
--treeClause3 c = clauseTree3 (clauseLhs c) (clauseRhs c)
--
--clauseTree3 = undefined
--
----clauseTree3 :: (Pretty t, Show t) => [SimplifiedPattern t] -> [([Stage6.SourceExpr t], Stage6.SourceExpr t)] -> Tree (Doc a)
----clauseTree3 ps gs = Node (pats <+> "=>") (guard <$> gs)
----  where
----    pats | 1 == length ps = pretty (head ps)
----         | otherwise      = "xxxx" -- foldr patternConx "" ps
----    guard ([], e) = exprTree3 e
----    guard (es, e) = Node (commaSep (iff <$> es)) [exprTree3 e]
----    iff e = "iff" <+> pretty e
------    guard ([], e)    = exprTree e
------    guard (es, e)    = Node (commaSep (iff <$> es)) [exprTree e]
------    iff e = "iff" <+> pretty e
--
--patternConx :: Name -> Doc a -> Doc a
--patternConx pat doc = pretty pat <+> doc
----patternCon :: Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Doc a -> Doc a
----patternCon pat doc = lhs <> rhs
----  where
----    lhs = parensIf addLeft (pretty pat)
----    rhs = if "" == show doc then "" else space <> doc
----    addLeft = case project pat of
----        PCon _ _ ps | not (null ps) -> True
----        PAs{}                       -> True
----        POr{}                       -> True
----        _                           -> False
--
--
--
----clauseTree ps gs = Node (pats <+> "=>") (guard <$> gs)
----  where
----    pats | 1 == length ps = pretty (head ps)
----         | otherwise      = foldr patternCon "" ps
----    guard ([], e)    = exprTree e
----    guard (es, e)    = Node (commaSep (iff <$> es)) [exprTree e]
----    iff e = "iff" <+> pretty e
--
--
--
--treeClause 
--  :: (Clauses [c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)))], FunArgs e2, Functor (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, Typed t22, LetBinding e1, Pretty e1, Pretty e2, Pretty t10, Pretty t12, Pretty t13, Pretty t14, Pretty t15, Pretty t16, Pretty t17, Pretty t18, Pretty t19, Pretty t20, Pretty t21, Pretty t22, Pretty t23, Pretty t25, PatternClause c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), PatternClause c2 t26 (Pattern t27 t28 t29 t30 t31 t32 t33 t34 t35) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)))) => c2 t26 (Pattern t27 t28 t29 t30 t31 t32 t33 t34 t35) (Expr t12 t13 t14 t15 t17 t18 t19 t16 t20 t10 t21 t22 t23 t24 t25 e1 e2 (c1 t11 (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))) -> Data.Tree.Tree (Doc ann)
--treeClause c = clauseTree (clauseLhs c) (clauseRhs c)
--
--withTag
--  :: (PatternClause c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed e1, LetBinding e1, Pretty e1, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t7, Pretty t8, Pretty t9, Pretty t10, Pretty t11, Pretty t12)
--  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))
--  -> Doc a
--withTag e = "" -- pretty e <+> colon <+> foo e -- (typeOf (exprTag e)) e
--  where
----    foo :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)) -> Text
----    foo = cata $ \case
----        EVar    t _     -> pretty t
----        ECon    t _ _   -> pretty t
----        ELit    t _     -> pretty t
----        EApp    t _     -> pretty t
----        ELet    t _ _ _ -> pretty t
------        EFix    t _ _ _ -> pretty t
------        ELam    t _ _   -> pretty t
----        EIf     t _ _ _ -> pretty t
----        EPat    t _ _   -> pretty t
------        EFun    t _     -> pretty t
----        EOp1    t _ _   -> pretty t
----        EOp2    t _ _ _ -> pretty t
------        ETuple  t _     -> pretty t
------        EList   t _     -> pretty t
----        _                -> "TODO"
--
----bindingTypeInfo
----  :: (Pretty bind)
----  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause
----  -> Guard (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause)
----bindingTypeInfo = undefined
----
----yyy
----  :: clause (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause)
----  -> Pattern u1 u2 u3 u4 u5 u6 u7 u8 u9
----yyy = undefined
--
----class C a where
----    xx :: a x -> Text
----    abc :: a x -> [p]
----    def :: a x -> [q]
----
----instance C (Clause t p) where
----    xx = undefined
----    abc (Clause t ps gs) = ps
----
------instance C (SimplifiedClause t p) where
------    xx = undefined
--
----clauseTree
----  :: (Typed bind, LetBinding bind, Functor clause, Pretty bind, Pretty t1, Pretty t2, Pretty t3, Pretty t4, Pretty t8, Pretty t10)
----  => [Pattern u1 u2 u3 u4 u5 u6 u7 u8 u9]
----  -> [Guard (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause)]
----  -> Tree (Doc a)
--clauseTree :: (PatternClause c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9) (Expr t11 t12 t13 t14 t15 t16 t17 t18 t19 t10 t20 t21 t22 t23 t24 bind lam (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9))), Functor (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)), Typed bind, Typed t21, LetBinding bind, Pretty bind, Pretty lam, Pretty t11, Pretty t12, Pretty t13, Pretty t14, Pretty t16, Pretty t18, Pretty t10, Pretty t15, Pretty t17, Pretty t19, Pretty t20, Pretty t21, Pretty t22, Pretty t24, Pretty a) => [Pattern t25 t26 t27 t28 t29 t30 t31 t32 t33] -> [([a], Expr t11 t12 t13 t14 t15 t16 t17 t18 t19 t10 t20 t21 t22 t23 t24 bind lam (c t (Pattern p1 p2 p3 p4 p5 p6 p7 p8 p9)))] -> Data.Tree.Tree (Doc ann)
--clauseTree ps gs = Node "TODO444" [] -- Node (pats <+> "=>") (guard <$> gs)
----  where
----    pats | 1 == length ps = pretty (head ps)
----         | otherwise      = foldr patternCon "" ps
----    guard ([], e)    = exprTree e
----    guard (es, e)    = Node (commaSep (iff <$> es)) [exprTree e]
----    iff e = "iff" <+> pretty e
--
----clauseTree :: (C clause) => clause (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause) -> Tree (Doc a)
----clauseTree c = undefined
----  where
----    ps = abc c
----    gs = def c
----
----    pats | 1 == length ps = pretty (head ps)
----         | otherwise      = foldr patternCon "" ps
----    guard (Guard [] e)    = exprTree e
----    guard (Guard es e)    = Node (commaSep (iff <$> es)) [exprTree e]
----    iff e = "iff" <+> pretty e
--
----xyz :: (Pretty p, Pretty t8) => p -> [(Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause, e)] -> Doc a
--xyz t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t
--
----withTag _ = ""
--
----clauseTree (Clause t ps gs) = Node pats (guard <$> gs)
----  where
----    pats | 1 == length ps = pretty (head ps)
----         | otherwise      = foldr patternCon "" ps
----    guard (Guard [] e)    = exprTree e
----    guard (Guard es e)    = Node (commaSep (iff <$> es)) [exprTree e]
----    iff e = "iff" <+> pretty e
--
--
----withTag :: Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 bind lam clause -> Doc a
----withTag e = annotated (typeOf (exprTag e)) e
--
--
----    EApp    t es         -> Node (annotated t ("@" :: Text)) (snd <$> es) -- (annotated t (appExpr t (fst <$> es))) []
----    ELet    t bind e1 e2 -> letTree t bind (snd e1) (snd e2)
----    EFix    t name e1 e2 -> Node "fix TODO" []
----    ELam    t ps e       -> Node "lam TODO" []
----    EIf     t e1 e2 e3   -> ifTree t (snd e1) (snd e2) (snd e3)
----    EPat    t es cs      -> Node (xyz t es) (clauseTree <$> (fst <$$> cs))
----    EFun    t cs         -> Node (annotated t ("fun" :: Text)) (clauseTree <$> (fst <$$> cs))
----    EOp1    t (ONeg _) a -> op1Tree t ("negate" :: Text) (snd a)
----    EOp1    t (ONot _) a -> op1Tree t ("not" :: Text) (snd a)
----    EOp2    t op a b     -> op2Tree t op (snd a) (snd b)
----    ETuple  t es         -> Node (pretty t) (snd <$> es)
----    EList   t es         -> Node (pretty t) (snd <$> es)
----    ERecord t row        -> Node ("#Record" <+> pretty t) (foo <$> concatRowWithKey row)
--
--class LetBinding b where
--    printLetBinding :: b -> Text
--    bindingTypeInfo :: b -> TypeInfo [Error]
--
----instance (Pretty b) => LetBinding (Binding (TypeInfoT [Error] Type) b) where
--instance (Typed t, Pretty t, Pretty b) => LetBinding (Binding (TypeInfoT [Error] t) b) where
--    printLetBinding = prettyPrint
--    bindingTypeInfo (BPat t _)   = undefined -- (nodeType t)
--    bindingTypeInfo (BFun t _ _) = undefined -- t
--
--instance LetBinding (ProgBinding (Maybe Type)) where
--    printLetBinding = prettyPrint
--    bindingTypeInfo _ = undefined -- TypeInfo (tVar kTyp "a") [] []
--
----instance (Pretty b) => LetBinding (Binding (TypeInfoT [Error] (Maybe Type)) b) where
----    printLetBinding = prettyPrint
----    bindingTypeInfo (BPat t _)   = fmap fromJust t
----    bindingTypeInfo (BFun t _ _) = fmap fromJust t
--
--instance LetBinding Void where
--    printLetBinding = prettyPrint
--    bindingTypeInfo _ = undefined -- TypeInfo (tVar kTyp "a") [] []
--
----letTree
----  :: (Pretty t, Typed b, LetBinding b)
----  => t
----  -> b
----  -> Tree (Doc a)
----  -> Tree (Doc a)
----  -> Tree (Doc a)
----letTree t bind e1 e2 =
----    Node (annotated t ("let" :: Text))
----        [ Node (annotated (bindingTypeInfo bind) (printLetBinding bind) <+> equals) [e1]
----        , Node "in" [e2] ]
--
----concatRowWithKey :: Row e -> [(Name, e)]
----concatRowWithKey (Row m _) = f =<< Map.foldrWithKey (curry (:)) mempty m
----  where
----    f (n, es) = [(n, e) | e <- es]
----
----foo :: (Name, (ProgExpr t, Tree (Doc a))) -> Tree (Doc a)
----foo (a, b) = Node (pretty a) [snd b]
----
----xyz :: (Typed t, Pretty p) => p -> [(ProgExpr t, e)] -> Doc a
----xyz t es = "match" <+> commaSep (withTag . fst <$> es) <+> "with" <+> colon <+> pretty t
--
--annotated :: (Pretty t, Pretty p) => t -> p -> Doc a
--annotated t p = pretty p <+> colon <+> pretty t
--
----withTag :: (Typed t) => ProgExpr t -> Doc a
----withTag e = annotated (typeOf (exprTag e)) e
----
----clauseTree :: (Typed t, Pretty t) => Clause t (ProgPattern t) (ProgExpr t) -> Tree (Doc a)
------clauseTree (Clause t ps gs) = Node (pats <+> colon <+> pretty t) (guard <$> gs)
----clauseTree (Clause t ps gs) = Node pats (guard <$> gs)
----  where
----    pats | 1 == length ps = pretty (head ps)
----         | otherwise      = foldr patternCon "" ps
----    guard (Guard [] e)    = exprTree e
----    guard (Guard es e)    = Node (commaSep (iff <$> es)) [exprTree e]
----    iff e = "iff" <+> pretty e
----
------op1Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a)
----op1Tree t op a = Node (annotated t op) [a]
----
------op2Tree :: (Typed t, Pretty p) => t -> p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
----op2Tree t op a b = Node ("(" <> pretty op <> ")" <+> colon <+> pretty t) [a, b]
----
----letTree :: (Pretty t1, Pretty t2, Pretty p) => t1 -> Binding t2 p -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
----letTree t bind e1 e2 =
----    Node (annotated t ("let" :: Text))
----        [ Node (annotated (bindingTag bind) bind <+> equals) [e1]
----        , Node "in" [e2]
----        ]
----
----ifTree :: (Pretty t) => t -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a) -> Tree (Doc a)
----ifTree t e1 e2 e3 =
----    Node (annotated t ("if" :: Text))
----        [ e1
----        , Node "then" [e2]
----        , Node "else" [e3]
----        ]
--
--instance (Pretty t) => Pretty (TypeInfoT [Error] t) where
--    pretty (TypeInfo es t ps) = pretty t <> preds <> errs
--      where
--        preds | null ps   = ""
--              | otherwise = space <> pretty ps
--        errs  | null es   = ""
--              | otherwise = space <> "TODO" -- <> pretty (parens . pretty <$$> es)
--
---- TODO
--instance Pretty Error where
--    pretty = \case 
--        CannotUnify t1 t2 err -> ("CannotUnify [" <> pretty t1 <> "] ~ [" <> pretty t2 <> "] " <> pretty err)
--        e -> pretty (show e)
--
--instance Pretty UnificationError where
--    pretty = \case 
--        e -> pretty (show e)
