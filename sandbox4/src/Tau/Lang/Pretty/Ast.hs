{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module Tau.Lang.Pretty.Ast where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Tau.Comp.Type.Inference
import Tau.Lang.Core
import Tau.Lang.Expr
import Tau.Lang.Pretty
import Tau.Lang.Type
import Tau.Util
import qualified Data.Text as Text

prettyAst :: (Pretty t, Show t, Pretty n, Pretty o) => Ast t n o -> Tree (Doc a)
prettyAst = para $ \case

    EPat t [] eqs -> 
        Node "fun" (prettyClauseTree =<< fst <$$> eqs)

    EPat t exs eqs -> 
        Node (foldl exprDoc "match" (fst <$> exs) <+> "with") 
             (prettyClauseTree =<< fst <$$> eqs)

    EDot t (a, _) (b, _) -> 
        Node ((pretty a <> dot <> pretty b) <+> colon <+> pretty t) []

    ERec t (FieldSet fields) -> 
        Node (pretty (recordCon (fieldName <$> fields)) <+> colon <+> pretty t) 
             (prettyFieldTree <$> fields)

    ERec2 t fields r -> 
        Node "TODO12" []

    ELst t elems ->
        Node (prettyList_ (pretty . fst <$> elems) <+> colon <+> pretty t) []

    a -> case snd <$> a of

        EVar t var -> 
            Node (pretty var <+> colon <+> pretty t) []

        ECon t con exprs -> 
            Node (pretty con <+> colon <+> pretty t) exprs

        ELit t lit -> 
            Node (pretty lit <+> colon <+> pretty t) []

        EApp t exprs -> 
            Node ("(@)" <+> colon <+> pretty t) exprs

        ELet t (BLet pat) e1 e2 -> 
            Node (patternDoc "let" pat <+> colon <+> pretty t) [prefix "=" e1, Node "in" [e2]]

        ELet t (BFun f ps) e1 e2 -> 
            Node (foldl patternDoc ("let" <+> pretty f) ps <+> colon <+> pretty t) [prefix "=" e1, Node "in" [e2]]

        EFix t name e1 e2 -> 
            Node ("fix" <+> pretty name) [prefix "=" e1, Node "in" [e2]]

        EOp1 t op a ->
            Node (pretty op <+> colon <+> pretty t) [a]

        EOp2 t op a b ->
            Node ("(" <> pretty op <> ")" <+> colon <+> pretty t) [a, b]

        ETup t elems -> 
            Node (pretty (tupleCon (length elems))) elems

        EIf t cond tr fl -> 
            Node ("if" <+> colon <+> pretty t) [cond, prefix "then" tr, prefix "else" fl]

        ELam t pats e1 -> 
            Node (foldl patternDoc "λ" pats <+> colon <+> pretty t) [prefix "=>" e1]

exprDoc :: (Pretty t, Pretty p, Pretty q, Pretty n, Pretty o) => Doc a -> Expr t p q r n o c d -> Doc a
exprDoc out expr = out <+> parens (pretty expr <+> colon <+> pretty (exprTag expr))

patternDoc :: (Pretty t) => Doc a -> Pattern t f g -> Doc a
patternDoc out pat = out <+> parens (pretty pat <+> colon <+> pretty (patternTag pat))

prettyClauseTree :: (Pretty t, Show t, Pretty n, Pretty o) => Clause (Pattern t f g) (Ast t n o) -> [Tree (Doc a)]
prettyClauseTree (Clause ps [Guard exs e]) =
    [Node (foldl patternDoc "─┬" ps) (whens <> [prefix "=>" (prettyAst e)])]
  where
    whens 
      | null exs  = []
      | otherwise = [Node "when" (prettyAst <$> exs)]
prettyClauseTree (Clause ps _) = 
    [Node ":::TODO:::" []]

prettyFieldTree :: (Pretty t, Pretty n, Pretty o) => Field t (Ast t n o, Tree (Doc a)) -> Tree (Doc a)
prettyFieldTree (Field t name (val, _)) = 
    Node (pretty name <+> equals <+> pretty val <+> colon <+> pretty t) []

prefix :: Text -> Tree (Doc a) -> Tree (Doc a)
prefix txt (Node label forest) = Node (pretty txt <+> label) forest

suffix :: Tree (Doc a) -> Text -> Tree (Doc a)
suffix (Node label forest) txt = Node (label <+> pretty txt) forest

nodesToString :: Tree (Doc a) -> Tree String
nodesToString = fmap (Text.unpack . renderDoc)

prettyCoreTree :: Core -> Tree (Doc a)
prettyCoreTree = para $ \case

    CPat (expr, _) eqs ->
        Node ("match" <+> pretty expr <+> "with") 
            (patternClause =<< fst <$$> eqs)

    a -> case snd <$> a of

        CVar var -> 
            Node (pretty var) []

        CLit lit -> 
            Node (pretty lit) []

        CApp exprs -> 
            Node "(@)" exprs

        CLet var e1 e2 -> 
            Node ("let" <+> pretty var) [prefix "=" e1, Node "in" [e2]]

        CLam var e1 ->
            Node ("λ" <> pretty var) [prefix "=>" e1]

        CIf cond tr fl -> 
            Node "if" [cond, prefix "then" tr, prefix "else" fl]
  where
    patternClause :: ([Name], Core) -> [Tree (Doc a)]
    patternClause (ps, e) = 
        [Node (hsep (pretty <$> "─┬" : ps)) [prefix "=>" (prettyCoreTree e)]]

--prettyClauseTree_ :: Clause Name Core -> [Tree (Doc a)]
--prettyClauseTree_ (Clause ps exs e) =
--    [Node (hsep (pretty <$> "─┬" : ps)) (whens <> [prefix "=>" (prettyCore e)])]
--  where
--    whens 
--      | null exs  = []
--      | otherwise = [Node "when" (prettyCore <$> exs)]
