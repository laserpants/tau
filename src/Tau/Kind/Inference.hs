{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Kind.Inference
  ( KindAssumption
  , inferKind
  , runInferKind
  ) where

import Control.Monad.Except
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Maybe (fromJust)
import Tau.Env
import Tau.Solver
import Tau.Type
import Tau.Util
import qualified Tau.Env as Env

type KindAssumption = Assumption Kind

tellAssumption
  :: (MonadWriter ([KindAssumption], [KindConstraint]) m)
  => Name
  -> Kind
  -> m ()
tellAssumption name kind = tell ([Assumption (name, kind)], mempty)

tellConstraint
  :: (MonadWriter ([KindAssumption], [KindConstraint]) m)
  => KindConstraint
  -> m ()
tellConstraint constraint = tell (mempty, [constraint])

runInferKind :: Env Kind -> Type -> Either UnificationError Kind
runInferKind env = 
    fromJust 
    . flip evalSupply (nameSupply "") 
    . runExceptT 
    . inferKind env

inferKind
  :: (MonadSupply Name m, MonadError UnificationError m)
  => Env Kind
  -> Type
  -> m Kind
inferKind env ty = do
    (kind, (as, cs)) <- runWriterT (infer ty)
    sub <- solveKinds (cs <> envConstraints as)
    pure (apply sub kind)
  where
    envConstraints :: [KindAssumption] -> [KindConstraint]
    envConstraints as = do
         (x, k) <- getAssumption <$> as
         (y, l) <- Env.toList env
         guard (x == y)
         pure (k, l)

infer
  :: (MonadSupply Name m, MonadWriter ([KindAssumption], [KindConstraint]) m)
  => Type
  -> m Kind
infer = cata $ \case
     ArrT t1 t2 -> do
         k1 <- t1
         k2 <- t2
         tellConstraint (k1, starK)
         tellConstraint (k2, starK)
         pure starK

     AppT t1 t2 -> do
         k1 <- t1
         k2 <- t2
         var <- varK <$> supply
         tellConstraint (k1, k2 `arrK` var)
         pure var

     ConT con | isPrim con ->
         pure starK

     ConT con -> do
         var <- varK <$> supply
         tellAssumption con var
         pure var

     VarT name -> do
         var <- varK <$> supply
         tellAssumption name var
         pure var

isPrim :: Name -> Bool
isPrim "Int"     = True
isPrim "Integer" = True
isPrim "Bool"    = True
isPrim "Float"   = True
isPrim "String"  = True
isPrim "Char"    = True
isPrim "Unit"    = True
isPrim "Void"    = True
isPrim _         = False
