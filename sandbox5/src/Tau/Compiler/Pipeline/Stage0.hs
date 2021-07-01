{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage0 where

import Control.Monad.Reader
import Data.Function ((&))
import Tau.Compiler.Error
import Tau.Compiler.Patterns
import Tau.Lang
import Tau.Prog
import Tau.Tooling
import Tau.Type

--runExhaustivePatternsCheck
--  :: ConstructorEnv 
--  -> ProgExpr (TypeInfoT [Error] (Maybe Type)) 
--  -> ProgExpr (TypeInfoT [Error] (Maybe Type))
--runExhaustivePatternsCheck env = flip runReader env . exhaustivePatternsCheck

exhaustivePatternsCheck
  :: (MonadReader ConstructorEnv m) 
  => ProgExpr (TypeInfoT [Error] (Maybe Type)) 
  -> m (ProgExpr (TypeInfoT [Error] (Maybe Type)))
exhaustivePatternsCheck = para $ \case

    EPat t expr clauses -> patExpr <$> check (fst <$$> clauses) t 
                                   <*> snd expr 
                                   <*> traverse sequence (snd <$$> clauses)

    EFun t clauses      -> funExpr <$> check (fst <$$> clauses) t 
                                   <*> traverse sequence (snd <$$> clauses)

    expr -> snd <$> expr & \case
        EVar    t var        -> pure (varExpr t var)
        ECon    t con exprs  -> conExpr t con <$> sequence exprs
        ELit    t prim       -> pure (litExpr t prim)
        EApp    t es         -> appExpr t <$> sequence es
        ELet    t bind e1 e2 -> letExpr t bind <$> e1 <*> e2
        EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
        ELam    t ps e       -> lamExpr t ps <$> e
        EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3
        EPat    t e cs       -> patExpr t <$> e <*> traverse sequence cs
        EFun    t cs         -> funExpr t <$> traverse sequence cs
        EOp1    t op a       -> op1Expr t op <$> a
        EOp2    t op a b     -> op2Expr t op <$> a <*> b
        ETuple  t es         -> tupleExpr t <$> sequence es
        EList   t es         -> listExpr t <$> sequence es
        ERow    t lab a b    -> rowExpr t lab <$> a <*> b 
  where
    check clauses ti = do
        exhaustive <- clausesAreExhaustive clauses
        pure (addErrors [NonExhaustivePatterns | not exhaustive] ti)
