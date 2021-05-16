{-# LANGUAGE LambdaCase #-}
module Tau.Compiler.Pipeline.Stage2 where

import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type

type SourceExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate 
  :: SourceExpr (TypeInfoT [Error] (Maybe Type))
  -> SourceExpr (Maybe Type)
translate = undefined

mapExpr :: (t -> u) -> SourceExpr t -> SourceExpr u
mapExpr f = cata $ \case
    EVar    t var          -> varExpr    (f t) var
    ECon    t con es       -> conExpr    (f t) con es
    ELit    t prim         -> litExpr    (f t) prim
    EApp    t es           -> appExpr    (f t) es
    EFix    t name e1 e2   -> fixExpr    (f t) name e1 e2
    ELam    t ps e         -> lamExpr    (f t) (mapPattern <$> ps) e
    EIf     t e1 e2 e3     -> ifExpr     (f t) e1 e2 e3
    EPat    t es cs        -> patExpr    (f t) es (mapClause <$> cs)
    ELet    t bind e1 e2   -> letExpr    (f t) (mapBind bind) e1 e2
  where
    mapBind = \case
        BLet    t p          -> BLet       (f t) (mapPattern p)
        BFun    t name ps    -> BFun       (f t) name (mapPattern <$> ps)

    mapClause = \case
        SimplifiedClause t ps g -> SimplifiedClause (f t) (mapPattern <$> ps) g

    mapPattern = cata $ \case
        PVar    t var        -> varPat     (f t) var
        PCon    t con ps     -> conPat     (f t) con ps
        PLit    t prim       -> litPat     (f t) prim
        PAs     t as p       -> asPat      (f t) as p
        POr     t p q        -> orPat      (f t) p q
        PAny    t            -> anyPat     (f t)
        PTuple  t ps         -> tuplePat   (f t) ps
        PList   t ps         -> listPat    (f t) ps
--            PRecord t row        -> recordPat  (f t) row
