{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
module Tau.PrettyTree where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Tau.Expr
import Tau.Expr.Main
import Tau.Pretty
import Tau.Util
import qualified Data.Text as Text

debugTree :: (Pretty t) => PatternExpr t -> IO ()
debugTree expr = putStrLn (showTree (Text.unpack <$> toTree_ expr))

toTree_ :: (Pretty t) => Expr t (Pattern t) (Pattern t) -> Tree Text
toTree_ = prettyExprTree

prettyExprTree :: (Pretty t) => PatternExpr t -> Tree Text
prettyExprTree = para $ \case
    EVar t var        -> node t var []
    ECon t con exs    -> node t (conExpr t con (fst <$> exs)) []
    ELit t lit        -> node t lit []
    EApp t exs        -> node t ("(@)" :: String) (snd <$> exs)
    ELet t pat e1 e2  -> node t ("let" :: String) [ node (exprTag (fst e1)) (prettyPrint pat <> " = " <> prettyPrint (fst e1)) [], snd e2 ]
    ELam t pat e1     -> node t ("λ(" <> prettyPrint pat <> " : " <> prettyPrint (patternTag pat) <> ")") [snd e1]
    EIf  t cond tr fl -> node t ("if" :: String) [snd cond, snd tr, snd fl]
    ERec t fields     -> node t (recExpr t (fmap fst <$> fields)) []
    EMat t exs eqs    -> node t ("match " <> matchExprs (fst <$> exs) <> " with") (fromClause <$> eqs)
    _                 -> Node "Not implemented" []
  where
    node t ex = Node (prettyPrint ex <> " : " <> prettyPrint t)

    matchExprs :: (Pretty t) => [PatternExpr t] -> Text
    matchExprs = renderDoc . commaSep . (expr <$>) where
        expr ex = "(" <> pretty ex <> " : " <> pretty (exprTag ex) <> ")"

    fromClause :: Clause (Pattern t) (PatternExpr t, Tree Text) -> Tree Text
    fromClause cl = Node (renderDoc (lhs <+> "=>" <+> rhs)) [] where
        (lhs, rhs) = splitClause cl

    fromPattern :: (Pretty t) => Pattern t -> Tree Text
    fromPattern pat = flip cata pat $ \case
        PVar t var    -> node t var []
        PCon t con ps -> node t con ps
        PLit t lit    -> node t (prettyPrint lit) []
        PRec t _      -> node t (prettyPrint pat) []
        PAny t        -> node t ("_" :: String) []
