{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Compiler.Pipeline.Stage0 where

import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.Supply
import Data.Function ((&))
import Data.Maybe
import Tau.Compiler.Error
import Tau.Compiler.Patterns
import Tau.Lang
import Tau.Prog
import Tau.Util
import Tau.Type
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

hasErrors 
  :: ProgExpr (TypeInfoT [e] t)
  -> Bool
hasErrors = foldrExprTag (\ti rest -> rest || not (null (nodeErrors ti))) False 

--

runReducePredicates
  :: ClassEnv
  -> [Predicate] 
  -> Either UnificationError [Predicate]
runReducePredicates env ps =
    fromJust (evalSupply (reduce env ps) (numSupply "???"))  -- TODO

foo2
  :: (FreeIn t)
  => Context
  -> ConstructorEnv
  -> ClassEnv
  -> ProgExpr (TypeInfoT [Error] t) 
  -> ProgExpr (TypeInfoT [Error] t)
foo2 context constructorEnv classEnv = 
    mapExprTag $ \ti@TypeInfo{..} -> 
        case runReducePredicates classEnv (predicates nodeType <> nodePredicates) of
            Left err -> addErrors [CannotUnify tInt tInt err] ti  -- TODO
            Right qs -> ti{ nodePredicates = qs }
  where
    predicates t = do
        (var, kind) <- free t
        set <- maybeToList (Env.lookup var context)
        name <- Set.toList set
        pure (InClass name (tVar kind var))

--

runExhaustivePatternsCheck
  :: (Show t, Eq t, RowType t) 
  => ConstructorEnv 
  -> ProgExpr (TypeInfoT [Error] t) 
  -> ProgExpr (TypeInfoT [Error] t)
runExhaustivePatternsCheck env = flip runReader env . exhaustivePatternsCheck

exhaustivePatternsCheck
  :: (Show t, Eq t, RowType t, MonadReader ConstructorEnv m) 
  => ProgExpr (TypeInfoT [Error] t) 
  -> m (ProgExpr (TypeInfoT [Error] t))
exhaustivePatternsCheck = para $ \case

    EPat t expr clauses -> 
        patExpr <$> check clausesAreExhaustive (fst <$$> clauses) t 
                <*> snd expr 
                <*> traverse sequence (snd <$$> clauses)

    EFun t clauses -> 
        funExpr <$> check clausesAreExhaustive (fst <$$> clauses) t 
                <*> traverse sequence (snd <$$> clauses)

    expr -> snd <$> expr & \case

        ELet t bind@(BPat _ p) e1 e2 -> 
            letExpr <$> check exhaustive [[p]] t
                    <*> pure bind 
                    <*> e1 
                    <*> e2

        ELet t bind@(BFun _ _ ps) e1 e2 -> 
            letExpr <$> check andM [exhaustive [[p]] | p <- ps] t
                    <*> pure bind
                    <*> e1
                    <*> e2

        ELam t ps e -> 
            lamExpr <$> check andM [exhaustive [[p]] | p <- ps] t
                    <*> pure ps
                    <*> e

        EHole   t            -> pure (holeExpr t)
        EVar    t var        -> pure (varExpr t var)
        ECon    t con exprs  -> conExpr t con <$> sequence exprs
        ELit    t prim       -> pure (litExpr t prim)
        EApp    t es         -> appExpr t <$> sequence es
        EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
        EIf     t e1 e2 e3   -> ifExpr t <$> e1 <*> e2 <*> e3
        EOp1    t op a       -> op1Expr t op <$> a
        EOp2    t op a b     -> op2Expr t op <$> a <*> b
        ETuple  t es         -> tupleExpr t <$> sequence es
        EList   t es         -> listExpr t <$> sequence es
        ERow    t lab a b    -> rowExpr t lab <$> a <*> b 

  where
    check f as ti = do
        exhaustive <- f as
        pure (addErrors [NonExhaustivePatterns | not exhaustive] ti)
