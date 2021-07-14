{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage3 where

import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Maybe (fromJust)
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Util
import Tau.Type

type SourceExpr t = Expr t t t t t t t t t Void Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

type TargetExpr t = Expr t t t t t t t t Void Void Void Void Void Void Void Void
    Void Name (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

runTranslate :: Supply Name a -> a
runTranslate expr = fromJust (evalSupply expr (numSupply "#"))

translate :: (MonadSupply Name m) => SourceExpr (Maybe Type) -> m (TargetExpr (Maybe Type))
translate = cata $ \case
    ELam t ps expr -> do
        e <- expr
        translateLambda t ps e

    ELet t bind expr1 expr2 -> do
        e1 <- expr1
        e2 <- expr2
        translateLet t bind e1 e2

    -- Other expressions do not change, except sub-expressions
    EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
    EVar    t var        -> pure (varExpr t var)
    ECon    t con es     -> conExpr t con <$> sequence es
    ELit    t prim       -> pure (litExpr t prim)
    EApp    t es         -> appExpr t <$> sequence es
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3

translateLambda
  :: (MonadSupply Name m) 
  => Maybe Type
  -> [ProgPattern (Maybe Type)]
  -> TargetExpr (Maybe Type)
  -> m (TargetExpr (Maybe Type))
translateLambda t [Fix (PVar _ var)] e = pure (lamExpr t var e)
translateLambda t ps e = do
    fst <$> foldrM fn (e, targetExprTag e) ps
  where
    fn p (e, t) = do
        let t' = tArr <$> patternTag p <*> t
        var <- supply
        pure (lamExpr t' var (patExpr t 
                 (varExpr (patternTag p) var)
                 [SimplifiedClause t [p] (Guard [] e)]), t')

translateLet
  :: (MonadSupply Name m) 
  => Maybe Type
  -> ProgBinding (Maybe Type)
  -> TargetExpr (Maybe Type)
  -> TargetExpr (Maybe Type)
  -> m (TargetExpr (Maybe Type))
translateLet t (BPat _ (Fix (PVar _ var))) e1 e2 = pure (fixExpr t var e1 e2)
translateLet t bind e1 e2 = do
    (e, p) <- case bind of
                  BPat _ pat  -> pure (e1, pat)
                  BFun t f ps -> do
                      e <- translateLambda t ps e1
                      pure (e, varPat t f)
    pure (patExpr t e [SimplifiedClause t [p] (Guard [] e2)])

targetExprTag :: (Show t) => TargetExpr t -> t
targetExprTag = cata $ \case
    EVar t _     -> t
    ECon t _ _   -> t
    ELit t _     -> t
    EApp t _     -> t
    EFix t _ _ _ -> t
    ELam t _ _   -> t
    EIf  t _ _ _ -> t
    EPat t _ _   -> t
--    e            -> error (show e)
