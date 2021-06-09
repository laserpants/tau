{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tau.Env where

import Data.Map.Strict (Map)
import Prelude hiding (lookup, insert)
import Tau.Tooling
import qualified Data.Map.Strict as Map

newtype Env a = Env { getEnv :: Map Name a }
    deriving (Show, Eq, Semigroup, Monoid, Functor)

empty :: Env a
empty = Env mempty

insert :: Name -> a -> Env a -> Env a
insert var val (Env envMap) = Env (Map.insert var val envMap)

inserts :: [(Name, a)] -> Env a -> Env a
inserts = flip (foldr (uncurry insert))

insertWith :: (a -> a -> a) -> Name -> a -> Env a -> Env a
insertWith f var val (Env envMap) = Env (Map.insertWith f var val envMap)

fromList :: [(Name, a)] -> Env a
fromList = Env . Map.fromList

fromListWith :: (a -> a -> a) -> [(Name, a)] -> Env a
fromListWith f = Env . Map.fromListWith f

toList :: Env a -> [(Name, a)]
toList = Map.toList . getEnv

union :: Env a -> Env a -> Env a
union (Env a) (Env b) = Env (Map.union a b)

elems :: Env a -> [a]
elems (Env envMap) = Map.elems envMap

domain :: Env a -> [Name]
domain (Env envMap) = Map.keys envMap

lookup :: Name -> Env a -> Maybe a
lookup name (Env envMap) = Map.lookup name envMap

findWithDefault :: a -> Name -> Env a -> a
findWithDefault value key (Env envMap) = Map.findWithDefault value key envMap

findWithDefaultEmpty :: (Monoid a) => Name -> Env a -> a
findWithDefaultEmpty key (Env envMap) = Map.findWithDefault mempty key envMap

isMember :: Name -> Env a -> Bool
isMember name (Env envMap) = Map.member name envMap

update :: (a -> Maybe a) -> Name -> Env a -> Env a
update f name (Env envMap) = Env (Map.update f name envMap)

map :: (a -> b) -> Env a -> Env b
map f (Env envMap) = Env (Map.map f envMap)
