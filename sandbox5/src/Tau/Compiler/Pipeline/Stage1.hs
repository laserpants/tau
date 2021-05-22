{-# LANGUAGE LambdaCase #-}
module Tau.Compiler.Pipeline.Stage1 where

import Data.Void
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type

type TargetExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

type TargetSimplifiedClause t = 
    SimplifiedClause t (ProgPattern t) (TargetExpr t)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate
  :: ProgExpr (TypeInfoT [Error] (Maybe Type))
  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
translate = cata $ \case
    -- Translate tuples, lists, and records
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
    ERow    t exprs      -> foldRow t exprs
    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr t [prefixOp2 op, a, b]
    -- Expand pattern clause guards
    EPat    t es cs      -> patExpr t es (expandClause =<< cs)
    EFun    t cs         -> translateFunExpr t (expandClause =<< cs)
    -- Other expressions do not change, except sub-expressions
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    ELam    t ps e       -> lamExpr t ps e
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
    ELet    t bind e1 e2 -> letExpr t bind e1 e2
  where
    prefixOp1 (ONeg t) = varExpr t "negate"
    prefixOp1 (ONot t) = varExpr t "not"
    prefixOp2 op       = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")
    expandClause (Clause t ps gs) 
                       = [SimplifiedClause t ps g | g <- gs]

foldRow 
  :: TypeInfoT [Error] (Maybe Type)
  -> [(Name, TargetExpr (TypeInfoT [Error] (Maybe Type)))]
  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
foldRow t exprs =
    fst (foldr fn (conExpr (t{ nodeType = Just tRowNil }) "{}" [], Just tRowNil) exprs)
  where
    fn (name, d) (e, ty) =
        let ty1 = tRowExtend name <$> nodeType (targetExprTag d) <*> ty
         -- in (rowCons (TypeInfo [] ty1 []) name d e, ty1)
         in (rowCons (t{ nodeType = ty1 }) name d e, ty1)

translateFunExpr
  :: TypeInfoT [Error] (Maybe Type)
  -> [TargetSimplifiedClause (TypeInfoT [Error] (Maybe Type))]
  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
translateFunExpr t =
    lamExpr t [varPat t1 "#0"] <<< patExpr t2 [varExpr t1 "#0"]
  where
    t1 = TypeInfo [] (get cod) (nodePredicates t)
    t2 = TypeInfo [] (get dom) (nodePredicates t)

    get :: (TypeF Kind Void Type -> Type) -> Maybe Type
    get f = fmap (f . project) (nodeType t)

    cod (TArr t1 _) = t1
    dom (TArr _ t2) = t2

targetExprTag :: TargetExpr t -> t
targetExprTag = cata $ \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    EFix t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
    EPat t _ _   -> t
    ELet t _ _ _ -> t
