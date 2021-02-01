{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tau.Env where

import Data.Map.Strict (Map)
import Tau.Util
import qualified Data.Map.Strict as Map

newtype Env a = Env { getEnv :: Map Name a }
    deriving (Show, Eq, Semigroup, Monoid)

empty :: Env a
empty = Env mempty

insert :: Name -> a -> Env a -> Env a
insert var val (Env env) = Env (Map.insert var val env)

inserts :: [(Name, a)] -> Env a -> Env a
inserts = flip (foldr (uncurry insert))

fromList :: [(Name, a)] -> Env a
fromList = Env . Map.fromList

fromListWith :: (a -> a -> a) -> [(Name, a)] -> Env a
fromListWith f = Env . Map.fromListWith f

toList :: Env a -> [(Name, a)]
toList = Map.toList . getEnv

union :: Env a -> Env a -> Env a
union (Env a) (Env b) = Env (Map.union a b)

elems :: Env a -> [a]
elems (Env env) = Map.elems env

domain :: Env a -> [Name]
domain (Env env) = Map.keys env

lookup :: Name -> Env a -> Maybe a
lookup name (Env env) = Map.lookup name env

findWithDefault :: a -> Name -> Env a -> a
findWithDefault value key (Env env) = Map.findWithDefault value key env

findWithDefaultEmpty :: (Monoid a) => Name -> Env a -> a
findWithDefaultEmpty key (Env env) = Map.findWithDefault mempty key env

isMember :: Name -> Env a -> Bool
isMember name (Env env) = Map.member name env

update :: (a -> Maybe a) -> Name -> Env a -> Env a
update f name (Env env) = Env (Map.update f name env)
