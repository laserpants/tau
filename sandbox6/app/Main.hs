{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
module Main where

import Control.Arrow
import Control.Monad.Supply
import Data.Functor.Foldable
import Data.Void
import Tau.Misc
import TextShow

main :: IO ()
main = print "done"

--

freshName :: (MonadSupply Int f m) => m Name
freshName = do 
    s <- demand
    pure ("a" <> showt s)

runTagTree :: ProgExpr t u -> ProgExpr Name u
runTagTree expr = runSupply (tagTree expr) succ 0

tagTree :: (MonadSupply Int f m) => ProgExpr t u -> m (ProgExpr Name u)
tagTree = cata alg 
  where
    alg expr = do
        t <- freshName
        case expr of

            EVar   _ var            -> pure (varExpr t var)
            ECon   _ con es         -> conExpr t con <$> sequence es
            ELit   _ prim           -> pure (litExpr t prim)
            EApp   _ es             -> appExpr t <$> sequence es
            EFix   _ name e1 e2     -> fixExpr t name <$> e1 <*> e2
            ELam   _ ps e           -> lamExpr t <$> traverse tagPattern ps <*> e
            EIf    _ e1 e2 e3       -> ifExpr t <$> e1 <*> e2 <*> e3
            EPat   _ e cs           -> patExpr t <$> e <*> traverse tagClause1 cs
            ELet   _ bind e1 e2     -> letExpr t <$> tagBinding bind <*> e1 <*> e2
            EFun   _ cs             -> funExpr t <$> traverse tagClause cs
            EOp1   _ op a           -> op1Expr t <$> tagOp1 op <*> a
            EOp2   _ op a b         -> op2Expr t <$> tagOp2 op <*> a <*> b
            ETuple _ es             -> tupleExpr t <$> sequence es
            EList  _ es             -> listExpr t <$> sequence es
            ERow   _ name e r       -> rowExpr t name <$> e <*> r
            EHole  _                -> pure (holeExpr t)
            EAnn   t a              -> annExpr t <$> a

    tagPattern = cata alg
      where
        alg pat = do
            t <- freshName
            case pat of

                PVar   _ var        -> pure (varPat t var)
                PCon   _ name ps    -> conPat t name <$> sequence ps
                PAs    _ name p     -> asPat t name <$> p
                PLit   _ prim       -> pure (litPat t prim)
                PAny   _            -> pure (anyPat t)
                POr    _ p q        -> orPat t <$> p <*> q
                PTuple _ ps         -> tuplePat t <$> sequence ps
                PList  _ ps         -> listPat t <$> sequence ps
                PRow   _ name p r   -> rowPat t name <$> p <*> r
                PAnn   t p          -> annPat t <$> p

    tagBinding bind = do
        t <- freshName
        case bind of

            BPat _ p                -> BPat t <$> tagPattern p
            BFun _ name ps          -> BFun t name <$> traverse tagPattern ps

    tagClause (Clause _ ps guards) = 
        Clause <$> freshName <*> traverse tagPattern ps <*> traverse sequence guards 

    tagClause1 (Clause _ p guards) = 
        Clause <$> freshName <*> tagPattern p <*> traverse sequence guards

    tagOp1 op = do
        t <- freshName
        pure $ case op of

            ONeg   _    -> ONeg   t
            ONot   _    -> ONot   t

    tagOp2 op = do
        t <- freshName
        pure $ case op of

            OEq    _    -> OEq    t
            ONeq   _    -> ONeq   t
            OAnd   _    -> OAnd   t
            OOr    _    -> OOr    t
            OAdd   _    -> OAdd   t
            OSub   _    -> OSub   t
            OMul   _    -> OMul   t
            ODiv   _    -> ODiv   t
            OPow   _    -> OPow   t
            OMod   _    -> OMod   t
            OLt    _    -> OLt    t
            OGt    _    -> OGt    t
            OLte   _    -> OLte   t
            OGte   _    -> OGte   t
            OLarr  _    -> OLarr  t
            ORarr  _    -> ORarr  t
            OFpp   _    -> OFpp   t
            OBpp   _    -> OBpp   t
            OOpt   _    -> OOpt   t
            OStr   _    -> OStr   t
            ODot   _    -> ODot   t
            OField _    -> OField t

--




test1 =
    runSupply (tagTree tree) (+1) 0
  where
    tree = 
        appExpr ()
            [ op2Expr () (OAdd ()) (holeExpr ()) (holeExpr ())
            , annExpr tInt (litExpr () (TInteger 5))
            , annExpr tInt (litExpr () (TInteger 5))
            ]




-- tagTree :: (MonadSupply Int f m) => ProgExpr t u -> m (ProgExpr Name u)
-- tagTree = cata alg 
--   where
--     alg expr = do
--         t <- freshName
--         case expr of
-- 
--             EVar _ var -> 
--                 pure (varExpr t var)
-- 
--             ECon _ con es ->
--                 conExpr t con <$> sequence es
-- 
--             ELit _ prim ->          
--                 pure (litExpr t prim)
-- 
--             EApp _ es ->
--                 appExpr t <$> sequence es
-- 
--             EFix _ name e1 e2 ->
--                 fixExpr t name <$> e1 <*> e2
-- 
--             ELam _ ps e ->
--                 lamExpr t <$> traverse tagPattern ps <*> e
-- 
--             EIf _ e1 e2 e3 ->
--                 ifExpr t <$> e1 <*> e2 <*> e3
-- 
--             EPat _ e cs ->
--                 patExpr t <$> e <*> traverse tagClause1 cs
-- 
--             ELet _ bind e1 e2 ->
--                 letExpr t <$> tagBinding bind <*> e1 <*> e2
-- 
--             EFun _ cs -> 
--                 funExpr t <$> traverse tagClause cs
-- 
--             EOp1 _ op a -> 
--                 op1Expr t <$> tagOp1 op <*> a
-- 
--             EOp2  _ op a b -> 
--                 op2Expr t <$> tagOp2 op <*> a <*> b
-- 
--             ETuple _ es ->
--                 tupleExpr t <$> sequence es
-- 
--             EList _ es ->
--                 listExpr t <$> sequence es
-- 
--             ERow _ name e r ->
--                 rowExpr t name <$> e <*> r
-- 
--             EHole _ ->
--                 pure (holeExpr t)
-- 
--             EAnn t a ->
--                 annExpr t <$> a
-- 
--     tagPattern :: (MonadSupply Int f m) => ProgPattern t u -> m (ProgPattern Name u)
--     tagPattern = cata alg
--       where
--         alg pat = do
--             t <- freshName
--             case pat of
-- 
--                 PVar _ var -> 
--                     pure (varPat t var)
-- 
--                 PCon _ name ps ->
--                     conPat t name <$> sequence ps
-- 
--                 PAs _ name p ->   
--                     asPat t name <$> p
-- 
--                 PLit _ prim ->
--                     pure (litPat t prim)
-- 
--                 PAny _ ->
--                     pure (anyPat t)
-- 
--                 POr _ p q ->
--                     orPat t <$> p <*> q
-- 
--                 PTuple _ ps ->
--                     tuplePat t <$> sequence ps
-- 
--                 PList _ ps ->
--                     listPat t <$> sequence ps
-- 
--                 PRow _ name p r ->
--                     rowPat t name <$> p <*> r
--                 
--                 PAnn t p ->
--                     annPat t <$> p
-- 
--     tagBinding bind = do
--         t <- freshName
--         case bind of
--             BPat _ p       -> BPat t <$> tagPattern p
--             BFun _ name ps -> BFun t name <$> traverse tagPattern ps
-- 
--     tagClause (Clause _ ps guards) = 
--         Clause <$> freshName <*> traverse tagPattern ps <*> traverse sequence guards 
-- 
--     tagClause1 (Clause _ p guards) = 
--         Clause <$> freshName <*> tagPattern p <*> traverse sequence guards
-- 
--     tagOp1 op = do
--         t <- freshName
--         pure $ case op of
-- 
--             ONeg   _ -> ONeg t
--             ONot   _ -> ONot t
-- 
--     tagOp2 op = do
--         t <- freshName
--         pure $ case op of
-- 
--             OEq    _ -> OEq    t
--             ONeq   _ -> ONeq   t
--             OAnd   _ -> OAnd   t
--             OOr    _ -> OOr    t
--             OAdd   _ -> OAdd   t
--             OSub   _ -> OSub   t
--             OMul   _ -> OMul   t
--             ODiv   _ -> ODiv   t
--             OPow   _ -> OPow   t
--             OMod   _ -> OMod   t
--             OLt    _ -> OLt    t
--             OGt    _ -> OGt    t
--             OLte   _ -> OLte   t
--             OGte   _ -> OGte   t
--             OLarr  _ -> OLarr  t
--             ORarr  _ -> ORarr  t
--             OFpp   _ -> OFpp   t
--             OBpp   _ -> OBpp   t
--             OOpt   _ -> OOpt   t
--             OStr   _ -> OStr   t
--             ODot   _ -> ODot   t
--             OField _ -> OField t

