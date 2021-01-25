{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StrictData                 #-}
module Lib4 where

import Control.Monad.Reader
import Control.Monad.Supply
import Control.Monad.Writer
import Tau.Expr
import Tau.Type
import Tau.Type.Class
import Tau.Type.Inference
import Tau.Util


infer2
  :: (MonadSupply Name m) 
  => ClassEnv a
  -> [Assumption]
  -> Expr t (Pattern t) (Pattern t) 
  -> m (Expr Type (Pattern Name) (Pattern Name), [Predicate])
infer2 env as = cata $ \case

    EVar _ var -> do
--        scheme <- findAssumption var as
        pure (varExpr undefined "x", [])

