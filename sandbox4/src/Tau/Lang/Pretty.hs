{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Pretty where

import Control.Arrow ((>>>))
import Control.Monad
import Data.List (unfoldr)
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Tuple.Extra (both)
import Tau.Comp.Type.Inference
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Type
import Tau.Util
import qualified Data.Text as Text

class Parens t where
    needsParens :: t -> Bool

instance Parens Type where
    needsParens = project >>> \case
        TApp t1 t2 
            | Just True == (isTupleCon <$> con)  -> False
            | Just True == (isRecordCon <$> con) -> False
            | isCon t1                           -> False
          where
            con = leftmostCon t1
        TApp{} -> True
        TArr{} -> True
        _      -> False

instance Parens Kind where
    needsParens = project >>> \case
        KArr{} -> True
        _      -> False

instance Parens (Pattern t) where
    needsParens = project >>> \case
        PCon _ _ [] -> False
        PCon{}      -> True
        PAs{}       -> True
        POr{}       -> True
        _           -> False

instance Parens (Expr t p q r) where
    needsParens = project >>> \case
        ECon _ _ [] -> False
        ECon{}      -> True
        _           -> False

addParens :: (Parens p) => p -> Doc a -> Doc a
addParens el doc = if needsParens el then parens doc else doc

instance Pretty Literal where
    pretty = \case
        LUnit      -> parens mempty
        LBool b    -> pretty b
        LInt n     -> pretty n
        LInteger n -> pretty n
        LFloat f   -> pretty f
        LChar c    -> squotes (pretty c)
        LString s  -> dquotes (pretty s)

instance Pretty Type where
    pretty = para $ \case
        TApp (t1, doc1) (t2, doc2)
            | Just True == (isTupleCon <$> con) ->
                let (_:ts) = unfoldApp (tApp t1 t2)
                 in parens (commaSep (pretty <$> ts))
            | Just True == (isRecordCon <$> con) ->
                let (Fix (TCon _ con):ts) = unfoldApp (tApp t1 t2)
                    ns = recordFieldNames con
                 in prettyRecord colon (fieldSet (uncurry (Field ()) <$> zip ns (pretty <$> ts)))
            | otherwise ->
                doc1 <+> addParens t2 doc2
          where
            con = leftmostCon t1

        TArr (t1, doc1) (_, doc2) -> 
            addParens t1 doc1 <+> "->" <+> doc2

        TCon _ name -> pretty name
        TVar _ name -> pretty name

leftmostCon :: Type -> Maybe Name
leftmostCon = cata $ \case
    TCon _ con -> Just con
    TApp a _   -> a
    _          -> Nothing

-- TODO: move?
isTupleCon :: Name -> Bool
isTupleCon con = Just True == (allCommas <$> stripped con)
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

-- TODO: move?
isRecordCon :: Name -> Bool
isRecordCon con = ("{", "}") == fstLst con
  where
    fstLst ""  = ("", "")
    fstLst con = both Text.singleton (Text.head con, Text.last con)

unfoldApp :: Type -> [Type]
unfoldApp = para alg
  where
    alg (TApp (_, a) (_, b)) = a <> b
    alg (TArr (a, _) (b, _)) = [tArr a b]
    alg (TCon k c) = [tCon k c]
    alg (TVar k v) = [tVar k v]

unfoldArr :: Type -> [Type]
unfoldArr = para alg
  where
    alg (TArr (_, a) (_, b)) = a <> b
    alg (TApp (a, _) (b, _)) = [tApp a b]
    alg (TCon k c) = [tCon k c]
    alg (TVar k v) = [tVar k v]

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
            | otherwise  = parens (commaSep preds) <+> "=> "

        preds = [pretty c <+> pretty (instt (tGen ty)) | InClass c ty <- ps]

instance Pretty Predicate where
    pretty (InClass name ty) = pretty (tApp con ty)
      where
        con = tCon (kArr kTyp (fromJust (kindOf ty))) name

instance (Pretty t) => Pretty (NodeInfoT t) where
    pretty (NodeInfo ty ps) = 
        case ps of 
            [] -> pretty ty 
            _  -> parens (pretty ty <> comma <+> pretty ps)

instance Pretty Kind where
    pretty = para $ \case
        KTyp -> "*"
        KCls -> "#"
        KArr (k1, doc1) (_, doc2) -> addParens k1 doc1 <+> "->" <+> doc2

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var            -> pretty var
        PCon _ "(::)" [x, xs] -> pretty (fst x) <+> "::" <+> pretty (fst xs)
        PCon _ con []         -> pretty con
        PCon _ con ps         -> foldl conArg (pretty con) (fst <$> ps)
        PLit _ lit            -> pretty lit
        PRec _ fields         -> prettyRecord equals (snd <$> fields)
        PTup _ elems          -> prettyTuple (snd <$> elems)
        PAs  _ name p         -> pretty (fst p) <+> "as" <+> pretty name
        POr  _ p1 p2          -> pretty (fst p1) <+> "or" <+> pretty (fst p2)
        PAny _                -> "_"

conArg :: (Parens p, Pretty p) => Doc a -> p -> Doc a
conArg out el = out <+> addParens el (pretty el)

instance (Pretty t) => Pretty (Binding (Pattern t)) where
    pretty (BLet p)    = pretty p
    pretty (BFun f ps) = foldl conArg (pretty f) ps

instance (Pretty p, Pretty q) => Pretty (Expr t p q r) where
    pretty = para $ \case
        EVar _ var            -> pretty var
        ELit _ lit            -> pretty lit
        ECon _ "(::)" [x, xs] -> pretty (fst x) <+> "::" <+> pretty (fst xs)
        ECon _ con []         -> pretty con
        ECon _ con args       -> foldl conArg (pretty con) (fst <$> args)
        EApp _ _              -> "TODO:eapp"
        ELet _ b e1 e2        -> prettyLet "let" b e1 e2 -- "let" <+> pretty b <+> equals <+> snd e1 <+> "in" <+> snd e2
        EFix _ b e1 e2        -> prettyLet "fix" b e1 e2
        ELam _ ps e2          -> "TODO:lam" -- prettyLam ps e2
        EIf  _ _ _ _          -> "TODO:eif"
        EPat _ _ _            -> "TODO:epat"
        EOp1 _ op a           -> "TODO:eop1"
        EOp2 _ op a b         -> "TODO:" <+> pretty op <+> snd a <+> snd b
        EDot _ name e1        -> snd e1 <> dot <> pretty name
        ERec _ _              -> "TODO:erec"
        ETup _ _              -> "TODO:etup"

-- | Pretty printer for let expressions
prettyLet
  :: (Pretty p, Pretty q, Pretty l)
  => Doc a
  -> l
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

instance Pretty (Op2 t) where
    pretty = pretty . op2Symbol

---- | Pretty printer for lambda abstractions
--prettyLam :: (Pretty (Expr t p q r)) => Doc a -> (Expr t p q r, Doc a) -> Doc a
--prettyLam arg e1 = 
--    group (nest 2 (vsep 
--      [ backslash <> arg <+> "=>"
--      , pretty (fst e1)
--      ])
--    )

commaSep :: [Doc a] -> Doc a
commaSep = hsep . punctuate comma

prettyRecord :: Doc a -> FieldSet t (Doc a) -> Doc a
prettyRecord sep fset
    | null fields = braces ""
    | otherwise   = lbrace <+> commaSep (prettyField <$> fields) <+> rbrace
  where
    fields = fieldList fset
    prettyField (_, key, val) = pretty key <+> sep <+> val

--patternConArg :: Doc a -> (Pattern p, Doc a) -> Doc a
--patternConArg out (pat, doc) = out <+> addParens pat doc 
--conArg :: Doc a -> (Expr t p q r, Doc a) -> Doc a
--conArg out (expr, doc) = out <+> addParens expr doc 

prettyTuple :: [Doc a] -> Doc a
prettyTuple = parens . commaSep


instance Pretty Core where
    pretty = para $ \case
        CVar var ->
            pretty var
        CLit lit ->
            pretty lit
        CApp exprs -> 
            "TODO:CApp"
        CLet var e1 e2 ->
            prettyLet_ "let" var (snd e1) (snd e2)
        CLam var e1 ->
            "TODO:CLam"
        CIf cond tr fl ->
            "TODO:CIf"
        CPat e1 cs ->
            "TODO:CPat"

--prettyLet_
--  :: (Pretty p, Pretty q, Pretty l)
--  => Doc a
--  -> l
--  -> (Expr t p q r, Doc a)
--  -> (Expr t p q r, Doc a)
--  -> Doc a
prettyLet_ keyword p e1 e2 =
    group (vsep
        [ nest 2 (vsep
            [ keyword
            , pretty p <+> equals <+> e1
            , nest 2 (vsep ["in", e2])
            ])
        ])


