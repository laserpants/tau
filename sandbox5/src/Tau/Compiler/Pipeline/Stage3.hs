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
    ELam    t ps e       -> translateLambda t ps e
    ELet    t bind e1 e2 -> translateLet t bind e1 e2
    -- Other expressions do not change, except sub-expressions
    EPat    t es cs      -> patExpr t es cs
    EVar    t var        -> varExpr t var
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EApp    t es         -> appExpr t es
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3

translateLambda
  :: Maybe Type
  -> [ProgPattern (Maybe Type)]
  -> TargetExpr (Maybe Type)
  -> TargetExpr (Maybe Type)
translateLambda t [Fix (PVar _ var)] e = lamExpr t var e
translateLambda t ps e = fst (foldr fn (e, targetExprTag e) ps)
  where
    fn p (e, t) =
        let t' = tArr <$> patternTag p <*> t
         in (lamExpr t' "#0" (patExpr t [varExpr (patternTag p) "#0"] [SimplifiedClause t [p] (Guard [] e)]), t')

translateLet
  :: Maybe Type
  -> ProgBinding (Maybe Type)
  -> TargetExpr (Maybe Type)
  -> TargetExpr (Maybe Type)
  -> TargetExpr (Maybe Type)
translateLet t (BLet _ (Fix (PVar _ var))) e1 e2 = fixExpr t var e1 e2
translateLet t bind e1 e2 = 
    patExpr t [e] [SimplifiedClause t [p] (Guard [] e2)]
  where
    (e, p) = case bind of
        BLet _ pat   -> (e1, pat)
        BFun t f ps  -> (translateLambda t ps e1, varPat t f)

targetExprTag :: TargetExpr t -> t
targetExprTag = cata $ \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    EFix t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
