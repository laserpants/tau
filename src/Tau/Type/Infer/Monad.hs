{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Type.Infer.Monad where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Supply
import Data.Set.Monad (Set)
import Data.Text (pack)
import Tau.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Data.Set.Monad as Set

newtype Monoset = Monoset (Set Name)
    deriving (Show, Eq)

insertIntoMonoset :: Name -> Monoset -> Monoset
insertIntoMonoset var (Monoset set) = Monoset (Set.insert var set)

instance Free Monoset where
    free (Monoset set) = set

instance Substitutable Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . TVar =<< set)

type InferTStack m a = ReaderT Monoset (ExceptT InferError (SupplyT Type m)) a

newtype InferT m a = InferT (InferTStack m a) deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader Monoset
    , MonadSupply Type
    , MonadError InferError )

data InferError
    = CannotSolve
    | CannotUnify
    | ImplementationError
    | InfiniteType
    | UnboundVariable Name
    | EmptyCaseStatement
    deriving (Show, Eq)

instance (Monad m) => MonadFail (InferT m) where
    fail = const (throwError ImplementationError)

instance MonadTrans InferT where
    lift = InferT . lift . lift . lift

freshVars :: List Type
freshVars = TVar . pfxed <$> [1..] where
    pfxed count = "a" <> pack (show count)

runInferT :: (Monad m) => InferT m a -> m (Either InferError a)
runInferT (InferT a) =
    freshVars 
        $> Monoset mempty
        |> runReaderT a 
        |> runExceptT 
        |> evalSupplyT

type Infer a = InferT Identity a

runInfer :: Infer a -> Either InferError a
runInfer = runIdentity . runInferT
