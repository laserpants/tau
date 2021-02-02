{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Tau.Type.Substitution where

import Data.List (intersect)
import Data.Map.Strict (Map)
import Data.Void
import Prelude hiding (null)
import Tau.Type
import Tau.Util
import qualified Data.Map.Strict as Map

newtype SubstitutionT a = Sub { getSub :: Map Name (TypeT a) }
    deriving (Show, Eq)

type Substitution = SubstitutionT Void

instance Semigroup (SubstitutionT a) where
    (<>) = compose

instance Monoid (SubstitutionT a) where
    mempty = null

class Substitutable t a where
    apply :: SubstitutionT a -> t -> t

instance Substitutable t a => Substitutable [t] a where
    apply = fmap . apply

instance Substitutable (TypeT a) a where
    apply sub = cata $ \case
        TVar kind var -> withDefault (tVar kind var) var sub
        TArr t1 t2    -> tArr t1 t2
        TApp t1 t2    -> tApp t1 t2
        ty            -> embed ty

instance Substitutable (PredicateT a) a where
    apply sub (InClass name ty) = InClass name (apply sub ty)

instance Substitutable Scheme Int where
    apply sub (Forall ks ps ty) = Forall ks (apply sub ps) (apply sub ty)

null :: SubstitutionT a
null = Sub mempty

mapsTo :: Name -> TypeT a -> SubstitutionT a
mapsTo name val = Sub (Map.singleton name val)

fromList :: [(Name, TypeT a)] -> SubstitutionT a
fromList = Sub . Map.fromList

toList :: SubstitutionT a -> [(Name, TypeT a)]
toList = Map.toList . getSub

withDefault :: TypeT a -> Name -> SubstitutionT a -> TypeT a
withDefault d name = Map.findWithDefault d name . getSub

domain :: SubstitutionT a -> [Name]
domain (Sub sub) = Map.keys sub

compose :: SubstitutionT a -> SubstitutionT a -> SubstitutionT a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

merge :: (Eq a) => SubstitutionT a -> SubstitutionT a -> Maybe (SubstitutionT a)
merge s1 s2 
    | allEqual  = Just (Sub (getSub s1 `Map.union` getSub s2))
    | otherwise = Nothing
  where
    allEqual = all equal (domain s1 `intersect` domain s2)

    equal :: Name -> Bool
    equal v = let app = (`apply` tVar kTyp v) :: (Eq a) => SubstitutionT a -> TypeT a
               in app s1 == app s2
