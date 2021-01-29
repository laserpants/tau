{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleInstances #-}
module Tau.Pretty where

import Control.Arrow ((>>>), (<<<))
import Data.List (sortOn)
import Data.Maybe (fromJust)
import Data.Text.Prettyprint.Doc
import Tau.Expr
import Tau.Type
import Tau.Type.Class
import Tau.Util
import qualified Data.Text as Text

sugared :: Type -> Maybe (Doc a)
sugared ty =
   case args ty of
      (a:as) | isTuple  a -> Just (prettyTupleType as)
      (a:as) | isRecord a -> Just (prettyRecordType (project a) as)
      _                   -> Nothing
  where
    isTuple = cata $ \case 
        TCon _ n -> Text.head n == '(' && Text.last n == ')'
        _        -> False

    isRecord = cata $ \case
        TCon _ n -> Text.head n == '{' && Text.last n == '}'
        _        -> False

    prettyRecordType (TCon _ c) args = 
        let kvPair key val = pretty key <+> ":" <+> pretty val
            pairs = sortOn fst (zip (Text.split (== ',') names) args)
            names = fromJust (Text.stripSuffix "}" =<< Text.stripPrefix "{" c)
        in "{" <+> hsep (punctuate comma (uncurry kvPair <$> pairs)) <+> "}"

    prettyTupleType args = 
        "(" <> hsep (punctuate comma (pretty <$> args)) <> ")"

args :: Type -> [Type]
args ty = flip para ty $ \case
    TApp a b -> snd a <> snd b
    TArr a b -> [tArr (fst a) (fst b)]
    TCon k a -> [tCon k a]
    TVar k a -> [tVar k a]
    _        -> []

prettyType :: [Name] -> Type -> Doc a
prettyType bound ty = flip para ty $ \case
    TApp a b -> 
        case sugared ty of
            Just doc -> doc
            Nothing  -> snd a <+> cata rhs (fst b)
      where
        rhs = \case
            TApp{} -> parens (snd b)
            TArr{} -> parens (snd b)
            _      -> snd b

    TArr a b -> cata lhs (fst a) <+> "->" <+> snd b 
      where
        lhs = \case
            TArr{} -> parens (snd a)
            _      -> snd a
    TCon _ name -> pretty name
    TVar _ name -> pretty name
    TGen n      -> pretty (bound !! n)

instance Pretty Type where
    pretty = prettyType []

instance Pretty Kind where
    pretty = para $ \case
        KStar -> "*"
        KArr a b  -> cata lhs (fst a) <+> "->" <+> snd b 
          where
            lhs = \case
                KArr{} -> parens (snd a)
                _      -> snd a

instance Pretty Predicate where
    pretty (InClass name ty) = pretty name <+> pretty ty

instance Pretty Scheme where
    pretty scheme = forall <> classes <> prettyType (reverse bound) ty
      where 
        forall
            | null bound = ""
            | otherwise  = "forall " <> sep (pretty <$> bound) <> ". "

        classes
            | null prds = ""
            | otherwise = tupled prds <+> "=> "

        prds = [pretty c <+> pretty n | (n, cs) <- info, c <- cs]

        bound = fst <$> info

        (ty, info) = flip cata scheme $ \case
            Scheme t              -> (t, [])
            Forall _ n cs (s, xs) -> (s, (n, cs):xs)

instance Pretty Literal where
    pretty = \case
        LUnit      -> "()"
        LBool b    -> pretty b
        LInt n     -> pretty n
        LInteger n -> pretty n
        LFloat f   -> pretty f
        LChar c    -> squotes (pretty c)
        LString s  -> dquotes (pretty s)

instance Pretty (Pattern t) where
    pretty = para $ \case
        PVar _ var     -> pretty var
        PCon _ con []  -> pretty con
        PCon _ con ps  -> pretty con <+> hsep (foldr args [] ps)
        PLit _ lit     -> pretty lit
        PRec _ fields  -> prettyRecord fields
        PAny _         -> "_"
      where
        args :: (Pattern t, Doc a) -> [Doc a] -> [Doc a]
        args a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                PCon{}  -> parens (snd a)
                _       -> snd a

prettyRecord :: [Field t (f, Doc a)] -> Doc a
prettyRecord fields = 
    "{" <+> prettyFields (fmap snd <$> sortFields fields) <+> "}"
  where
    prettyFields fields = 
        hsep (punctuate comma (field <$> fields))
    field (Field _ key val) = 
        pretty key <+> "=" <+> val

instance Pretty (Op (PatternExpr t)) where
    pretty op = case op of
        OEq    a b -> binOp a b "=="
        ONEq   a b -> binOp a b "/="
        OAnd   a b -> binOp a b "&&"  
        OOr    a b -> binOp a b "||"  
        OAdd   a b -> binOp a b "+"   
        OSub   a b -> binOp a b "-"
        OMul   a b -> binOp a b "*"
        ODiv   a b -> binOp a b "/"
        OPow   a b -> binOp a b "^"
        OLt    a b -> binOp a b "<"
        OGt    a b -> binOp a b ">"
        OLtE   a b -> binOp a b "<="    
        OGtE   a b -> binOp a b ">="
        OLArr  a b -> binOp a b "<<" 
        ORArr  a b -> binOp a b ">>" 
        OFPipe a b -> binOp a b "|>"
        OBPipe a b -> binOp a b "<|"
        ODot   a b -> pretty a <> "." <> subOp AssocR b
        _          -> undefined
      where
        binOp a b symb = subOp AssocL a 
                     <+> symb 
                     <+> subOp AssocR b

        subOp :: Assoc -> PatternExpr t -> Doc a
        subOp assoc a = 
            let par ops = 
                  case compare (opPrecedence op) (opPrecedence ops) of
                      LT -> False
                      GT -> True
                      EQ -> assoc /= opAssoc op
             in flip cata a $ 
               \case
                 EApp{}              -> parens (pretty a)
                 ELet{}              -> parens (pretty a)
                 ELam{}              -> parens (pretty a)
                 EIf{}               -> parens (pretty a)
                 EOp _ ops | par ops -> parens (pretty a)
                 _                   -> pretty a

instance Pretty (PatternExpr t) where
    pretty = para $ \case
        EVar _ var     -> pretty var
        ECon _ con []  -> pretty con
        ECon _ con exs -> pretty con <+> hsep (foldr app [] exs)
        ELit _ lit     -> pretty lit
        EApp _ exs     -> hsep (foldr app [] exs)
        ELet _ p e1 e2 -> prettyLet p e1 e2
        ELam _ p e1    -> prettyLam p e1 
        EIf  _ c e1 e2 -> prettyIf c e1 e2
        EMat _ exs eqs -> prettyMatch exs eqs
        EOp  _ op      -> pretty (fst <$> op)
        ERec _ fields  -> prettyRecord fields
      where
        app :: (PatternExpr t, Doc a) -> [Doc a] -> [Doc a]
        app a = (rhs :)
          where
            rhs = flip cata (fst a) $ \case 
                EApp{} -> parens (snd a)
                ECon{} -> parens (snd a)
                _      -> snd a

prettyMatch 
  :: [(PatternExpr t, Doc a)] 
  -> [Clause (Pattern t) (PatternExpr t, Doc a)] 
  -> Doc a
prettyMatch exs eqs = 
    group (nest 2 (vsep 
        [ "match" <+> hsep (punctuate comma (snd <$> exs)) <+> "with"
        , case clause <$> zip lhss rhss of
              []   -> ""
              c:cs -> flatAlt (vsep ((pipe <+>) <$> c:cs)) 
                              (hsep (c:((pipe <+>) <$> cs)))
        ]))
  where
    (lhss, rhss) = unzip (split <$> eqs)
    colWidth     = maximum (length . show <$> lhss)

    clause (lhs, expr) =
        flatAlt (fillBreak colWidth lhs) lhs <+> "=>" <+> expr

    split (Clause ps exs e) = (commaSep ps <> when, pretty (fst e))
      where
        when | null exs  = ""
             | otherwise = space <> "when" <+> commaSep (fst <$> exs)

commaSep :: (Pretty p) => [p] -> Doc a
commaSep docs = hsep (punctuate comma (pretty <$> docs))

prettyLet 
  :: Pattern t 
  -> (PatternExpr t, Doc a) 
  -> (PatternExpr t, Doc a) 
  -> Doc a
prettyLet p e1 e = 
    group (vsep 
      [ nest 2 (vsep 
        [ "let"
        , pretty p <+> equals <+> expr
        , nest 2 (vsep ["in", body])
        ])
      ])
  where
    expr = pretty (fst e1)
    body = pretty (fst e)

prettyLam :: Pattern t -> (PatternExpr t, Doc a) -> Doc a
prettyLam p e1 = 
    group (nest 2 (vsep [backslash <> pattern_ p <+> "=>", pretty (fst e1)]))
  where
    pattern_ :: Pattern t -> Doc a
    pattern_ p = flip cata p $ \case
        PCon _ _ [] -> pretty p
        PCon{}      -> parens (pretty p)
        _           -> pretty p

prettyIf 
  :: (PatternExpr t, Doc a) 
  -> (PatternExpr t, Doc a) 
  -> (PatternExpr t, Doc a) 
  -> Doc a
prettyIf c e1 e2 = 
    group (nest 2 (vsep [if_, then_, else_]))
  where
    if_   = "if"   <+> pretty (fst c)
    then_ = "then" <+> pretty (fst e1)
    else_ = "else" <+> pretty (fst e2)
