{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Substitution where

import Data.List (intersect)
import Data.Map.Strict (Map)
import Prelude hiding (null)
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map

newtype Substitution a = Sub { getSub :: Map Name (TypeT a) }
    deriving (Show, Eq)

instance Semigroup (Substitution a) where
    (<>) = compose

instance Monoid (Substitution a) where
    mempty = null

type TypeSubstitution = Substitution Void

class Substitutable t a where
    apply :: Substitution a -> t -> t

instance Substitutable (TypeT a) a where
    apply sub = cata $ \case
        TVar kind var -> withDefault (tVar kind var) var sub
        TArr t1 t2    -> tArr t1 t2
        TApp t1 t2    -> tApp t1 t2
        ty            -> embed ty

null :: Substitution a
null = Sub mempty

mapsTo :: Name -> TypeT a -> Substitution a
mapsTo name val = Sub (Map.singleton name val)

withDefault :: TypeT a -> Name -> Substitution a -> TypeT a
withDefault def name = Map.findWithDefault def name . getSub

fromList :: [(Name, TypeT a)] -> Substitution a
fromList = Sub . Map.fromList

toList :: Substitution a -> [(Name, TypeT a)]
toList = Map.toList . getSub

domain :: Substitution a -> [Name]
domain (Sub sub) = Map.keys sub

compose :: Substitution a -> Substitution a -> Substitution a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

merge :: (Eq a) => Substitution a -> Substitution a -> Maybe (Substitution a)
merge s1 s2 
    | allEqual  = Just (Sub (getSub s1 `Map.union` getSub s2))
    | otherwise = Nothing
  where
    app :: (Eq a) => Substitution a -> Name -> TypeT a
    app sub var = apply sub (tVar kTyp var)

    allEqual = all (\v -> app s1 v == app s2 v) (domain s1 `intersect` domain s2)
