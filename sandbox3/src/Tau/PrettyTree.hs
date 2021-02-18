{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
module Tau.PrettyTree where

import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Tree
import Data.Tree.View (showTree)
import Data.Tuple.Extra (snd3)
import Tau.Expr
import Tau.Lang.Pretty
import Tau.Util
import qualified Data.Text as Text

debugTree :: (Monad m, Show t, Pretty t, Pretty p, Pretty q, Pretty r, Pretty (Expr t p q r)) => Expr t p q r -> m ()
debugTree expr = debug (showTree (Text.unpack <$> prettyExprTree expr) :: String)

xxx2 :: Text -> Tree Text -> Tree Text
xxx2 t (Node a b) = Node (t <> a) b

prettyExprTree :: (Show t, Pretty t, Pretty p, Pretty q, Pretty r, Pretty (Expr t p q r)) => Expr t p q r -> Tree Text
prettyExprTree = para $ \case
    EVar t var        -> node t var []
    ECon t con exs    -> node t (conExpr t con (fst <$> exs)) []
    ELit t lit        -> node t lit []
    EApp t exs        -> node t (text "(@)") (snd <$> exs)
    ELet t pat e1 e2  -> node t (text "let") [ Node (renderDoc (pretty pat <+> equals)) [snd e1], Node "in" [snd e2] ] --  <+> pretty (fst e1))) []
    EFix t name e1 e2 -> node t (text "fix") [ Node (renderDoc (pretty name <+> equals)) [snd e1], Node "in" [snd e2] ] --  <+> pretty (fst e1))) []

    ELam t pats e1    -> node t (renderDoc ("λ" <> pretty pats)) [snd e1]
    EIf  t cond tr fl -> node t (text "if") (snd <$> [cond, ("then " <>) <$$> tr, ("else " <>) <$$> fl])
    ERec t fields     -> node t ("{" <> Text.intercalate "," (fieldName <$> fields) <> "}") (field_ <$> fields) -- (fst <$$> fields)) []
    EPat t [] eqs     -> node t (renderDoc "fun") (clauseTree <$> eqs)
    EPat t exs eqs    -> node t (renderDoc ("match" <+> matchExprs (fst <$> exs) <+> "with")) (clauseTree <$> eqs)
    EOp t op          -> node t (fst <$> op) []
  where
    field_ (Field _ name e) = xxx2 (name <> " = ") (snd e) -- Node (renderDoc (pretty name)) [snd e]

    text :: Text -> Text
    text = id

    node t ex = renderNode (pretty ex <+> colon <+> pretty t)

    renderNode = Node . renderDoc 

    matchExprs = commaSep . (expr <$>) 
      where
        expr ex = parens (pretty ex <+> colon <+> pretty (exprTag ex))

    clauseTree cl = renderNode (lhs <+> "=>" <+> rhs) []
      where
        (lhs, rhs) = splitClause cl

--    patternTree :: (Pretty t) => Pattern t -> Tree Text
--    patternTree = para $ \case
--        PVar t var    -> node t var []
--        PCon t con ps -> node t con (snd <$> ps)
--        PLit t lit    -> node t lit []
--        PRec t fields -> node t (recPat t (fst <$$> fields)) []
--        PAny t        -> node t (text "_") []
