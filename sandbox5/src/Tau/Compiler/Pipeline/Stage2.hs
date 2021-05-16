{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleContexts #-}
module Tau.Compiler.Pipeline.Stage2 where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.List (nub)
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type
import qualified Data.Text as Text

type SourceExpr t = Expr t t t t t t t t t Void Void Void Void Void Void
    (ProgBinding t) [ProgPattern t] (SimplifiedClause t (ProgPattern t))

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

translate 
  :: SourceExpr (TypeInfoT [Error] (Maybe Type))
  -> SourceExpr (Maybe Type)
translate = undefined

expandTypeClasses
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => SourceExpr (TypeInfoT [e] t)
  -> StateT [(Name, Type)] m (SourceExpr (TypeInfoT [e] t))
expandTypeClasses expr = 
    insertDictArgs <$> run expr <*> (nub <$> pluck)
  where
    run
      :: ( MonadSupply Name m
         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
      => SourceExpr (TypeInfoT [e] t)
      -> StateT [(Name, Type)] m (SourceExpr (TypeInfoT [e] t))
    run = cata $ \case
        ELet t pat expr1 expr2 -> do
            undefined

        EVar t var ->
            undefined

        ELit t lit ->
            undefined

        e ->
            embed <$> sequence e

insertDictArgs
  :: SourceExpr (TypeInfoT [e] t)
  -> [(Name, Type)]
  -> SourceExpr (TypeInfoT [e] t)
insertDictArgs expr _ =
    expr
    -- TODO
--    undefined

applyDicts
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Predicate
  -> SourceExpr (TypeInfoT [e] t)
  -> StateT [(Name, Type)] m (SourceExpr (TypeInfoT [e] t))
applyDicts (InClass name ty) expr

    | isVar ty = do
        tv <- Text.replace "a" "$d" <$> supply
        undefined

    | otherwise = do
        env <- askClassEnv
        case classMethods <$> lookupClassInstance name ty env of
            Left e -> undefined -- throwError e
            Right methods -> do
                undefined

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
