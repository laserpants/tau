{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
module Tau.Compiler.Typecheck where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Set.Monad (Set)
import Tau.Compiler.Error
import Tau.Compiler.Substitution
import Tau.Compiler.Unification
import Tau.Env (Env(..))
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type

inferAst
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m )
  => Ast t 
  -> m (Ast TypeInfo)
inferAst = undefined

inferPattern
  :: ( MonadSupply Name m
     , MonadReader (ClassEnv, TypeEnv) m
     , MonadState (TypeSubstitution, Context) m
     , MonadError Error m ) 
  => ProgPattern t 
  -> WriterT [(Name, Type)] m (ProgPattern TypeInfo)
inferPattern = undefined

inferOp1 = undefined

inferOp2 = undefined

inferClause = undefined

primType :: Prim -> Type
primType = \case
    TUnit      -> tUnit
    TBool{}    -> tBool
    TInt{}     -> tInt
    TInteger{} -> tInteger
    TFloat{}   -> tFloat
    TDouble{}  -> tDouble
    TChar{}    -> tChar
    TString{}  -> tString

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Type class instances 

instance (Typed t) => Typed (ProgExpr t) where
    typeOf = typeOf . exprTag

instance (Typed t) => Typed (ProgPattern t) where
    typeOf = typeOf . patternTag

instance (Typed t) => Typed (Op1 t) where
    typeOf = typeOf . op1Tag

instance (Typed t) => Typed (Op2 t) where
    typeOf = typeOf . op2Tag

instance (Typed t) => Typed (Ast t) where
    typeOf = typeOf . astTag
