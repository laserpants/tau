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

type TypeSubstitution = Substitution Void

instance Semigroup (Substitution a) where
    (<>) = compose

instance Monoid (Substitution a) where
    mempty = null

class Substitutable t a where
    apply :: Substitution a -> t -> t

instance Substitutable t a => Substitutable [t] a where
    apply = fmap . apply

instance Substitutable (TypeT a) a where
    apply = substitute

instance Substitutable (PredicateT (TypeT a)) a where
    apply = fmap . apply

instance Substitutable PolyType (TypeT a) where
    apply (Sub sub) = substitute (Sub (Map.map upgrade sub))

instance Substitutable Scheme (TypeT a) where
    apply sub (Forall ks ps pt) = Forall ks ps (apply sub pt)

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

substitute :: Substitution a -> TypeT a -> TypeT a
substitute sub = cata $ \case
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
    allEqual = all (\v -> appV s1 v == appV s2 v) (domain s1 `intersect` domain s2)
    appV sub var = substitute sub (tVar kTyp var)
