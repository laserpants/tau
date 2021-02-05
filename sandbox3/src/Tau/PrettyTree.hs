{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
module Tau.PrettyTree where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Tau.Expr
import Tau.Pretty
import Tau.Util
import qualified Data.Text as Text

debugTree :: (Monad m, Pretty t) => PatternExpr t -> m ()
debugTree expr = debug (showTree (Text.unpack <$> toTree_ expr) :: String)

toTree_ :: (Pretty t) => Expr t (Pattern t) (Pattern t) -> Tree Text
toTree_ = prettyExprTree

prettyExprTree :: (Pretty t) => PatternExpr t -> Tree Text
prettyExprTree = para $ \case
    EVar t var        -> node t var []
    ECon t con exs    -> node t (conExpr t con (fst <$> exs)) []
    ELit t lit        -> node t lit []
    EApp t exs        -> node t (text "(@)") (snd <$> exs)
    ELet t pat e1 e2  -> node t (text "let") [ node (exprTag (fst e1)) (renderDoc (pretty pat <+> equals <+> pretty (fst e1))) []
                                             , snd e2 ]
    ELam t pat e1     -> node t (renderDoc ("λ" <> parens (pretty pat <+> colon <+> pretty (patternTag pat)))) [snd e1]
    EIf  t cond tr fl -> node t (text "if") (snd <$> [cond, tr, fl])
    ERec t fields     -> node t (recExpr t (fst <$$> fields)) []
    EMat t exs eqs    -> node t (renderDoc (matchExprs (fst <$> exs) <+> "with")) (clauseTree <$> eqs)
    _                 -> Node "Not implemented" []
  where
    text :: Text -> Text
    text = id

    node t ex = renderNode (pretty ex <+> colon <+> pretty t)

    renderNode = Node . renderDoc 

    matchExprs :: (Pretty t) => [PatternExpr t] -> Doc a
    matchExprs = commaSep . (expr <$>) 
      where
        expr ex = parens (pretty ex <+> colon <+> pretty (exprTag ex))

    clauseTree :: Clause (Pattern t) (PatternExpr t, Tree Text) -> Tree Text 
    clauseTree cl = renderNode (lhs <+> "=>" <+> rhs) []
      where
        (lhs, rhs) = splitClause cl

    patternTree :: (Pretty t) => Pattern t -> Tree Text
    patternTree = para $ \case
        PVar t var    -> node t var []
        PCon t con ps -> node t con (snd <$> ps)
        PLit t lit    -> node t lit []
        PRec t fields -> node t (recPat t (fst <$$> fields)) []
        PAny t        -> node t (text "_") []
