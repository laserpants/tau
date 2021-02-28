{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
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

prefix :: Text -> Tree (Doc a) -> Tree (Doc a)
prefix txt (Node label forest) = Node (pretty txt <+> label) forest

suffix :: Tree (Doc a) -> Text -> Tree (Doc a)
suffix (Node label forest) txt = Node (label <+> pretty txt) forest

yyy :: Tree (Doc a) -> Tree String
yyy = fmap (Text.unpack . renderDoc)

--xxx :: Tree (Doc a) -> Tree Text
--xxx = fmap renderDoc 

prettyAst :: (Pretty t, Show t) => Ast t -> Tree (Doc a)
prettyAst = para $ \case

    EPat t [] eqs  -> Node "fun" []
    EPat t exs eqs -> Node (foldl fonArg "match" (fst <$> exs) <+> "with") (prettyClauseTree =<< fst <$$> eqs)

    a -> case snd <$> a of

        EVar t var               -> Node (pretty var) []
        ECon t con exprs         -> Node (pretty con) exprs
        ELit t lit               -> Node (pretty lit) []
        EApp t exprs             -> Node "(@)" exprs
        ELet t (BLet pat) e1 e2  -> Node "let" [prettyPatternTree pat, prefix "=" e1, prefix "in" e2]
        ELet t (BFun f ps) e1 e2 -> Node "let" []
        EFix t name e1 e2        -> Node "fix" [Node (pretty name) [], prefix "=" e1, prefix "in" e2]
        ELam t pats e1           -> Node "λ" ((prettyPatternTree <$> pats) <> [Node "=>" [e1]])
        EIf  t cond tr fl        -> Node "if" [cond, prefix "then" tr, prefix "else" fl]
        EOp1 t ONot a            -> Node "not" [a]
        EOp1 t ONeg a            -> Node "negate" [a]
        EOp2 t op a b            -> Node (pretty (opSymbol op)) [a, b]
        EDot t name a            -> Node "TODO" []
        ERec t (FieldSet fields) -> Node (pretty (recordCon (fieldName <$> fields))) (prettyFieldTree <$> fields)
        ETup t elems             -> Node (pretty (tupleCon (length elems))) elems

--fonArg :: (Pretty t) => Doc a -> Expr t p q r -> Doc a
--fonArg out expr = out <+> addParens expr (pretty expr)
fonArg out expr = out <+> parens (pretty expr <+> colon <+> pretty (exprTag expr)) -- addParens expr (pretty expr)

prettyClauseTree :: (Pretty t, Show t) => Clause (Pattern t) (Ast t) -> [Tree (Doc a)]
prettyClauseTree (Clause ps exs e) = 
    undefined
--    (prettyPatternTree <$> ps) <> whens <> [Node "=>" [prettyAst e]]
--  where
--    whens 
--        | null exs  = []
--        | otherwise = [] -- [Node "when" exs]

prettyPatternTree :: Pattern t -> Tree (Doc a)
prettyPatternTree = cata $ \case

    PVar t var               -> Node (pretty var) []
    PCon t con ps            -> Node (pretty con) ps
    PLit t lit               -> Node (pretty lit) []
    PRec t (FieldSet fields) -> Node "" []
    PTup t elesm             -> Node "" []
    PAs  t name p            -> Node "" []
    POr  t a b               -> Node "" []
    PAny t                   -> Node "" []

prettyFieldTree :: Field t (Tree (Doc a)) -> Tree (Doc a)
prettyFieldTree (Field t name val) = Node (pretty name) [val]
