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
import Data.Maybe
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Util
import Tau.Type
import qualified Data.Map.Strict as Map

type TargetExpr t = Expr t t t t t t t t t Void Void Void Void Void Void Void
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

-- desugar
translate
  :: ProgExpr (TypeInfoT [e] (Maybe Type))
  -> TargetExpr (TypeInfoT [e] (Maybe Type))
translate = cata $ \case
    -- Translate tuples, lists, and row expressions
    ETuple  t exprs      -> conExpr t (tupleCon (length exprs)) exprs
    EList   t exprs      -> foldr (listExprCons t) (conExpr t "[]" []) exprs
    ERow    t lab a b    -> foldRowExpr t lab a b
    -- Translate operators to prefix form
    EOp1    t op a       -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b     -> translateAppExpr t [prefixOp2 op, a, b]
    -- Expand pattern clause guards and eliminate fun expressions
    EPat    t e cs       -> patExpr t e (expandClause =<< cs)
    EFun    t cs         -> translateFunExpr t (expandClause =<< cs)
    -- Remove holes in function application expressions
    EApp    t es         -> translateAppExpr t es
    -- Other expressions do not change, except sub-expressions
    EVar    t var        -> varExpr t var
    EHole   t            -> varExpr t "^" 
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
    expandClause (Clause t ps gs) = [SimplifiedClause t ps g | g <- gs]

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
  :: TypeInfoT [e] (Maybe Type) 
  -> [TargetExpr (TypeInfoT [e] (Maybe Type))] 
  -> TargetExpr (TypeInfoT [e] (Maybe Type))
translateAppExpr t es = 
    --foldr yyy (appExpr (TypeInfo [] (gork <$> nodeType t) []) replaceHoles) holes
    foldr yyy (appExpr t replaceHoles) holes
  where
    yyy (a, n) b = lamExpr 
        (xyz (nodeType (targetExprTag a)) <$> targetExprTag b) 
        [varPat (targetExprTag a) n] b

    xyz :: Maybe Type -> Maybe Type -> Maybe Type
    xyz a t = tArr <$> a <*> t

    replaceHoles = fromJust (evalSupply (mapM f es) [0..])
      where
        f e 
          | hole e = do
              n <- supply
              pure (varExpr (targetExprTag e) (xvar n))
          | otherwise = pure e

    hole (Fix (EVar _ "^")) = True
--    hole (Fix (EHole _))    = True
    hole _                  = False

    holes = zip (filter hole es) [xvar n | n <- [0..]]

    xvar n = "^" <> intToText n

--    gork = cata $ \case
--      TArr _ t -> t
--      s        -> embed s

translateFunExpr
  :: TypeInfoT [e] (Maybe Type)
  -> [TargetSimplifiedClause (TypeInfoT [e] (Maybe Type))]
  -> TargetExpr (TypeInfoT [e] (Maybe Type))
translateFunExpr t cs =
--    lamExpr t [varPat t1 "#0"] (patExpr t2 (varExpr t1 "#0") cs)

    lamExpr t [varPat (patternTag p) ("#" <> intToText n) | (p, n) <- zip ps [0..]] 
--              (varExpr (TypeInfo [] (Just tInt) []) "XX")
              (patExpr t5 xyz (gork <$> cs))
  where
    gork (SimplifiedClause t [p] gs) = 
        SimplifiedClause t [p] gs

    gork (SimplifiedClause t ps gs) = 
        SimplifiedClause t [p] gs
      where
        p = conPat (TypeInfo [] yy1 []) (tupleCon (length ps)) ps

    xyz = case zzz of
        [e] -> e
        es -> conExpr (TypeInfo [] yy1 []) (tupleCon (length es)) es

    yy1 = if any isNothing xx1 
              then Nothing
              else Just (tTuple (catMaybes xx1))

    xx1 = nodeType . patternTag <$> ps
        
    zzz = [varExpr (patternTag p) ("#" <> intToText n) | (p, n) <- zip ps [0..]]

    t1 = TypeInfo [] (get cod) []
    t2 = TypeInfo [] (get dom) []

    get :: (TypeF Kind Void Type -> Type) -> Maybe Type
    get f = fmap (f . project) (nodeType t)

    cod (TArr t1 _) = t1
    dom (TArr _ t2) = t2

    arity = length ps
    SimplifiedClause t5 ps _:_ = cs

targetExprTag :: TargetExpr t -> t
targetExprTag = cata $ \case
    EVar  t _     -> t
    ECon  t _ _   -> t
    ELit  t _     -> t
    EApp  t _     -> t
    EFix  t _ _ _ -> t
    ELam  t _ _   -> t
    EIf   t _ _ _ -> t
    EPat  t _ _   -> t
    ELet  t _ _ _ -> t
