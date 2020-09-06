{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tau.Env where

import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.Map.Strict as Map

type Name = Text

newtype Env a = Env { getEnv :: Map Name a }
    deriving (Show, Eq, Semigroup, Monoid)

insert :: Name -> a -> Env a -> Env a
insert var val (Env env) = Env (Map.insert var val env)

insertMany :: [(Name, a)] -> Env a -> Env a
insertMany = flip (foldr (uncurry insert))

fromList :: [(Name, a)] -> Env a
fromList = Env . Map.fromList

union :: Env a -> Env a -> Env a
union (Env a) (Env b) = Env (Map.union a b)

elems :: Env a -> [a]
elems (Env env) = Map.elems env

lookup :: Name -> Env a -> Maybe a
lookup name (Env env) = Map.lookup name env

findWithDefault :: a -> Name -> Env a -> a
findWithDefault value key (Env env) = Map.findWithDefault value key env

findWithDefaultEmpty :: (Monoid a) => Name -> Env a -> a
findWithDefaultEmpty key (Env env) = Map.findWithDefault mempty key env
