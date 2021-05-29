{-# LANGUAGE LambdaCase #-}
module Tau.Compiler.Pipeline.Stage4 where

import Data.Maybe (fromMaybe)
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
    compileClause (SimplifiedClause t ps g) =
        SimplifiedClause t (translatePatterns <$> ps) g

--    compileClause
--      :: SimplifiedClause t (ProgPattern t) a
--      -> SimplifiedClause t (Pattern t t t t t t Void Void Void) a

type IntermPattern = Pattern (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) (Maybe Type) Void Void Void

--translatePatterns :: ProgPattern t -> Pattern t t t t t t Void Void Void
translatePatterns :: ProgPattern (Maybe Type) -> IntermPattern
translatePatterns = cata $ \case
    -- Translate tuples, lists, and row patterns
    PTuple  t ps         -> conPat t (tupleCon (length ps)) ps
    PList   t ps         -> foldr (listPatCons t) (conPat t "[]" []) ps
    PRow    t lab p q    -> foldRowPattern t lab p q
    -- Remaining patterns stay the same, except sub-patterns
    PVar    t var        -> varPat   t var
    PCon    t con ps     -> conPat   t con ps
    PLit    t prim       -> litPat   t prim
    PAs     t as p       -> asPat    t as p
    POr     t p q        -> orPat    t p q
    PAny    t            -> anyPat   t

foldRowPattern :: Maybe Type -> Name -> IntermPattern -> Maybe IntermPattern -> IntermPattern 
foldRowPattern t lab p q = conPat t ("{" <> lab <> "}") 
    [ p
    , fromMaybe (conPat (Just tRowNil) "{}" []) q ]

--foldRow :: Maybe Type -> [(Name, IntermPattern)] -> IntermPattern
--foldRow t pats =
--    fst (foldr fn (conPat (Just tRowNil) "{}" [], Just tRowNil) pats)
--  where
--    fn (name, o) (p, ty) = 
--        let ty1 = tRowExtend name <$> intremPatternTag o <*> ty
--         in (rowPatCons ty1 name o p, ty1)

intremPatternTag :: IntermPattern -> Maybe Type
intremPatternTag = cata $ \case
    PVar    t _    -> t
    PCon    t _ _  -> t 
    PLit    t _    -> t 
    PAs     t _ _  -> t 
    POr     t _ _  -> t 
    PAny    t      -> t
