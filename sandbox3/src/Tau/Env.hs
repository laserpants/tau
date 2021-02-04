{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tau.Env where

import Data.Map.Strict (Map)
import Prelude hiding (lookup, insert)
import Tau.Util
import qualified Data.Map.Strict as Map

newtype Env a = Env { getEnv :: Map Name a }
    deriving (Show, Eq, Semigroup, Monoid, Functor)

empty :: Env a
empty = Env mempty

insert :: Name -> a -> Env a -> Env a
insert var val (Env emap) = Env (Map.insert var val emap)

inserts :: [(Name, a)] -> Env a -> Env a
inserts = flip (foldr (uncurry insert))

insertWith :: (a -> a -> a) -> Name -> a -> Env a -> Env a
insertWith f var val (Env emap) = Env (Map.insertWith f var val emap)

fromList :: [(Name, a)] -> Env a
fromList = Env . Map.fromList

fromListWith :: (a -> a -> a) -> [(Name, a)] -> Env a
fromListWith f = Env . Map.fromListWith f

toList :: Env a -> [(Name, a)]
toList = Map.toList . getEnv

union :: Env a -> Env a -> Env a
union (Env a) (Env b) = Env (Map.union a b)

elems :: Env a -> [a]
elems (Env emap) = Map.elems emap

domain :: Env a -> [Name]
domain (Env emap) = Map.keys emap

lookup :: Name -> Env a -> Maybe a
lookup name (Env emap) = Map.lookup name emap

findWithDefault :: a -> Name -> Env a -> a
findWithDefault value key (Env emap) = Map.findWithDefault value key emap

findWithDefaultEmpty :: (Monoid a) => Name -> Env a -> a
findWithDefaultEmpty key (Env emap) = Map.findWithDefault mempty key emap

isMember :: Name -> Env a -> Bool
isMember name (Env emap) = Map.member name emap

update :: (a -> Maybe a) -> Name -> Env a -> Env a
update f name (Env emap) = Env (Map.update f name emap)

map :: (a -> b) -> Env a -> Env b
map f (Env emap) = Env (Map.map f emap)

copyKey :: Name -> Name -> Env a -> Env a
copyKey old new emap = case lookup old emap of
    Nothing  -> emap
    Just val -> insert new val emap
