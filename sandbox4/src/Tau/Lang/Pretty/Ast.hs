{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Lang.Pretty.Ast where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Tau.Comp.Type.Inference
import Tau.Lang.Expr
import Tau.Lang.Pretty
import Tau.Lang.Type
import Tau.Util
import qualified Data.Text as Text

prettyAst :: (Pretty t, Show t) => Ast t -> Tree (Doc a)
prettyAst = para $ \case

    EPat t [] eqs -> 
        Node "fun" (prettyClauseTree =<< fst <$$> eqs)

    EPat t exs eqs -> 
        Node (foldl exprDoc "match" (fst <$> exs) <+> "with") 
             (prettyClauseTree =<< fst <$$> eqs)

    EDot t name (a, _) -> 
        Node (pretty a <> dot <> pretty name <+> colon <+> pretty t) []

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
            Node (patternDoc "let" pat) [prefix "=" e1, Node "in" [e2]]

        ELet t (BFun f ps) e1 e2 -> 
            Node (foldl patternDoc ("let" <+> pretty f) ps) [prefix "=" e1, Node "in" [e2]]

        EFix t name e1 e2 -> 
            Node ("fix" <+> pretty name) [prefix "=" e1, Node "in" [e2]]

        EOp1 t ONot a -> 
            Node "not" [a]

        EOp1 t ONeg a -> 
            Node "negate" [a]

        EOp2 t op a b ->
            Node ("(" <> pretty (opSymbol op) <> ")" <+> colon <+> pretty t) [a, b]

        ETup t elems -> 
            Node (pretty (tupleCon (length elems))) elems

        ERec t (FieldSet fields) -> 
            Node (pretty (recordCon (fieldName <$> fields))) 
                 (prettyFieldTree <$> fields)

        EIf t cond tr fl -> 
            Node "if" [cond, prefix "then" tr, prefix "else" fl]

        ELam t pats e1 -> 
            Node (foldl patternDoc "λ" pats) [prefix "=>" e1]

exprDoc :: (Pretty t, Pretty p, Pretty q) => Doc a -> Expr t p q r -> Doc a
exprDoc out expr = out <+> parens (pretty expr <+> colon <+> pretty (exprTag expr))

patternDoc :: (Pretty t) => Doc a -> Pattern t -> Doc a
patternDoc out pat = out <+> parens (pretty pat <+> colon <+> pretty (patternTag pat))

prettyClauseTree :: (Pretty t, Show t) => Clause (Pattern t) (Ast t) -> [Tree (Doc a)]
prettyClauseTree (Clause ps exs e) =
    [Node (foldl patternDoc "─┬" ps) (whens <> [prefix "=>" (prettyAst e)])]
  where
    whens 
      | null exs  = []
      | otherwise = [Node "when" (prettyAst <$> exs)]

prettyFieldTree :: Field t (Tree (Doc a)) -> Tree (Doc a)
prettyFieldTree (Field t name val) = Node (pretty name) [val]

prefix :: Text -> Tree (Doc a) -> Tree (Doc a)
prefix txt (Node label forest) = Node (pretty txt <+> label) forest

suffix :: Tree (Doc a) -> Text -> Tree (Doc a)
suffix (Node label forest) txt = Node (label <+> pretty txt) forest

nodesToString :: Tree (Doc a) -> Tree String
nodesToString = fmap (Text.unpack . renderDoc)
