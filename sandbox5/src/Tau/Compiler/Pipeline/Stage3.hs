{-# LANGUAGE LambdaCase #-}
module Tau.Compiler.Pipeline.Stage3 where

import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Type
import Tau.Tool

type SourceExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

type TargetExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate :: SourceExpr (Maybe Type) -> TargetExpr (Maybe Type)
translate = cata $ \case
    ELam    t ps e       -> undefined -- unrollLambda2 t ps e
    ELet    t bind e1 e2 -> undefined -- unrollLet2 t bind e1 e2
    -- Other expressions do not change, except sub-expressions
    EPat    t es cs      -> patExpr t es cs
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3

