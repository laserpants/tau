{-# LANGUAGE LambdaCase #-}
module Tau.Compiler.Pipeline.Stage4 where

import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Type
import Tau.Tool

type SourceExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (ProgPattern t))

type TargetExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (Pattern t t t t t t Void Void Void))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate :: SourceExpr (Maybe Type) -> TargetExpr (Maybe Type)
translate = cata $ \case
    ELam    t ps e       -> lamExpr t ps e
    EPat    t es cs      -> patExpr t es (compileClause <$> cs)
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
  where
    compileClause
      :: SimplifiedClause t (ProgPattern t) a
      -> SimplifiedClause t (Pattern t t t t t t Void Void Void) a
    compileClause (SimplifiedClause t ps g) =
        SimplifiedClause t (translatePatterns <$> ps) g

translatePatterns :: ProgPattern t -> Pattern t t t t t t Void Void Void
translatePatterns = cata $ \case
    -- Translate tuples, lists, and record patterns
    PTuple  t ps         -> conPat t (tupleCon (length ps)) ps
    PList   t ps         -> foldr (listPatCons t) (conPat t "[]" []) ps
    -- Remaining patterns stay the same, except sub-patterns
    PVar    t var        -> varPat   t var
    PCon    t con ps     -> conPat   t con ps
    PLit    t prim       -> litPat   t prim
    PAs     t as p       -> asPat    t as p
    POr     t p q        -> orPat    t p q
    PAny    t            -> anyPat   t
