{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Tau.Env where

import Data.Map.Strict (Map)
import Data.Set.Monad (Set)
import Data.Text (Text)
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

type Name = Text

newtype Env a = Env { getEnv :: Map Name a }
    deriving (Show, Eq, Semigroup, Monoid)

insert :: Name -> a -> Env a -> Env a
insert var val (Env map) = Env (Map.insert var val map)

insertMany :: [(Name, a)] -> Env a -> Env a
insertMany = flip (foldr (uncurry insert))

fromList :: [(Name, a)] -> Env a
fromList = Env . Map.fromList

union :: Env a -> Env a -> Env a
union (Env a) (Env b) = Env (Map.union a b)

elems :: Env a -> [a]
elems (Env map) = Map.elems map

lookup :: Name -> Env a -> Maybe a
lookup name (Env map) = Map.lookup name map

findWithDefault :: a -> Name -> Env a -> a
findWithDefault value key (Env map) = Map.findWithDefault value key map

findWithDefaultEmpty :: (Monoid a) => Name -> Env a -> a
findWithDefaultEmpty key (Env map) = Map.findWithDefault mempty key map
