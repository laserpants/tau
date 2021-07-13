{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage1 where

import Control.Monad.Supply
import Data.List (partition)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, fromJust)
import Data.Tuple.Extra (second)
import Data.Void
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Tooling
import Tau.Type
import qualified Data.Map.Strict as Map

type TargetExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

type TargetSimplifiedClause t = 
    SimplifiedClause t (ProgPattern t) (TargetExpr t)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--rowToMap :: [(Name, ProgExpr t)] -> Map Name [ProgExpr t]
--rowToMap = foldr fn mempty 
--  where
--    fn = undefined -- TODO 
----    fn ("*", Fix (ERow _ exprs)) m = undefined
----    fn (label, expr) m = Map.insertWith (<>) label [expr] m
--
----rowToMap :: [(Name, ProgExpr t)] -> Map Name [ProgExpr t]
----rowToMap = Map.fromListWith (<>) .  fmap (second pure) 
----
----flattenMap :: Map Name [ProgExpr t] -> Map Name [ProgExpr t]
----flattenMap tmap = 
----    case Map.lookup "*" tmap of
----        Just [Fix (ERow _ row)] -> 
----            Map.foldrWithKey (Map.insertWith (<>)) 
----                             (Map.delete "*" tmap) 
----                             (rowToMap row)
----        _ -> 
----            tmap
--
--mapToRow :: Map Name [ProgExpr t] -> [(Name, ProgExpr t)]
--mapToRow rmap = do
--    (label, exprs) <- Map.toList rmap
--    expr <- exprs
--    pure (label, expr)
--
--translate
--  :: ProgExpr (TypeInfoT [Error] (Maybe Type))
--  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
--translate = translate2 . translate1
--translate = translate2 . translate1
--
---- TODO ???
--translate1
--  :: ProgExpr (TypeInfoT [Error] (Maybe Type))
--  -> ProgExpr (TypeInfoT [Error] (Maybe Type))
--translate1 = cata $ \case
--    EVar    t var        -> varExpr   t var
--    ECon    t con es     -> conExpr   t con es
--    ELit    t prim       -> litExpr   t prim
--    EApp    t es         -> appExpr   t es
--    ELet    t bind e1 e2 -> letExpr   t bind e1 e2
--    EFix    t name e1 e2 -> fixExpr   t name e1 e2
--    ELam    t ps e       -> lamExpr   t ps e
--    EIf     t e1 e2 e3   -> ifExpr    t e1 e2 e3
--    EPat    t es cs      -> patExpr   t es cs
--    EFun    t cs         -> funExpr   t cs
--    EOp1    t op a       -> op1Expr   t op a
--    EOp2    t op a b     -> op2Expr   t op a b
--    ETuple  t es         -> tupleExpr t es
--    EList   t es         -> listExpr  t es
--    ERow    t lab a b    -> rowExpr   t lab a b 

translate
  :: ProgExpr (TypeInfoT [Error] (Maybe Type))
  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
translate = cata $ \case
    -- Translate tuples, lists, and row expressions
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
    ERow    t lab a b    -> foldRowExpr t lab a b
    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> appExpr t [prefixOp2 op, a, b]
    -- Expand pattern clause guards
    EPat    t e cs       -> patExpr t e (expandClause =<< cs)
    EFun    t cs         -> translateFunExpr t (expandClause =<< cs)

    EApp    t es         -> translateAppExpr t es
--    EApp    t es         -> appExpr t es

    -- Other expressions do not change, except sub-expressions
    EVar    t var        -> varExpr t var
    EHole   t            -> holeExpr t 
    ECon    t con es     -> conExpr t con es
    ELit    t prim       -> litExpr t prim
    EFix    t name e1 e2 -> fixExpr t name e1 e2
    ELam    t ps e       -> lamExpr t ps e
    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
    ELet    t bind e1 e2 -> letExpr t bind e1 e2
  where
    prefixOp1 (ONeg t)    = varExpr t "negate"
    prefixOp1 (ONot t)    = varExpr t "not"
    prefixOp2 (OField t)  = varExpr t "@#getField"
    prefixOp2 op          = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")
    expandClause (Clause t p gs) = [SimplifiedClause t [p] g | g <- gs]

--foldRow 
--  :: TypeInfoT [Error] (Maybe Type)
--  -> Name
--  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
--  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
--  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
--foldRow t label a b = conExpr t ("{" <> label <> "}") [a, b]

--    [ a
--    , b -- undefined -- fromMaybe (conExpr (TypeInfo [] (Just tRowNil) []) "{}" []) b ]
--    ]

--foldRow 
--  :: TypeInfoT [Error] (Maybe Type)
--  -> [(Name, TargetExpr (TypeInfoT [Error] (Maybe Type)))]
--  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
--foldRow t exprs =
--    fst (foldr fn (conExpr (t{ nodeType = Just tRowNil }) "{}" [], Just tRowNil) exprs)
--  where
--    fn (name, d) (e, ty) =
--        let ty1 = tRowExtend name <$> nodeType (targetExprTag d) <*> ty
--         -- in (rowExprCons (TypeInfo [] ty1 []) name d e, ty1)
--         in (rowExprCons (t{ nodeType = ty1 }) name d e, ty1)

-- [varExpr () "(+)", x, y]

translateAppExpr 
  :: TypeInfoT [Error] (Maybe Type) 
  -> [TargetExpr (TypeInfoT [Error] (Maybe Type))] 
  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
translateAppExpr t es = 
    foldr yyy (appExpr (TypeInfo [] (gork <$> nodeType t) []) replaceHoles) holes
  where
    yyy (a, n) b = lamExpr (xyz (nodeType (targetExprTag a)) <$> targetExprTag b) [varPat (targetExprTag a) n] b

    xyz :: Maybe Type -> Maybe Type -> Maybe Type
    xyz a t = tArr <$> a <*> t

    replaceHoles = fromJust (evalSupply (mapM f es) [0..])
      where
        f e 
          | isHole e = do
              n <- supply
              pure (varExpr (targetExprTag e) (xvar n))
          | otherwise = pure e

    holes = zip (filter isHole es) [xvar n | n <- [0..]]

    xvar n = "^" <> intToText n

    gork = cata $ \case
      TArr _ t -> t
      s        -> embed s

translateFunExpr
  :: TypeInfoT [Error] (Maybe Type)
  -> [TargetSimplifiedClause (TypeInfoT [Error] (Maybe Type))]
  -> TargetExpr (TypeInfoT [Error] (Maybe Type))
translateFunExpr t =
    lamExpr t [varPat t1 "#0"] <<< patExpr t2 (varExpr t1 "#0")
  where
    t1 = TypeInfo [] (get cod) []
    t2 = TypeInfo [] (get dom) []

    get :: (TypeF Kind Void Type -> Type) -> Maybe Type
    get f = fmap (f . project) (nodeType t)

    cod (TArr t1 _) = t1
    dom (TArr _ t2) = t2

targetExprTag :: TargetExpr t -> t
targetExprTag = cata $ \case
    EVar  t _     -> t
    EHole t       -> t
    ECon  t _ _   -> t
    ELit  t _     -> t
    EApp  t _     -> t
    EFix  t _ _ _ -> t
    ELam  t _ _   -> t
    EIf   t _ _ _ -> t
    EPat  t _ _   -> t
    ELet  t _ _ _ -> t
