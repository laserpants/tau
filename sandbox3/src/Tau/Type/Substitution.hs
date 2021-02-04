{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
module Tau.Type.Substitution where

import Data.List (intersect)
import Data.Map.Strict (Map)
import Prelude hiding (null)
import Tau.Type
import Tau.Util
import qualified Data.Map.Strict as Map

newtype SubstitutionT a = Sub { getSub :: Map Name a }
    deriving (Show, Eq)

type Substitution = SubstitutionT Type

instance Semigroup (SubstitutionT (TypeT a)) where
    (<>) = compose

instance Monoid (SubstitutionT (TypeT a)) where
    mempty = null

class Substitutable t a where
    apply :: SubstitutionT a -> t -> t

instance Substitutable t a => Substitutable [t] a where
    apply = fmap . apply

instance Substitutable (PredicateT (TypeT a)) (TypeT a) where
    apply = fmap . apply

instance Substitutable Scheme Type where
    apply sub (Forall ks ps ty) = Forall ks ps (apply sub ty)

instance Substitutable (TypeT a) (TypeT a) where
    apply sub = cata $ \case
        TVar kind var -> withDefault (tVar kind var) var sub
        TArr t1 t2    -> tArr t1 t2
        TApp t1 t2    -> tApp t1 t2
        ty            -> embed ty

instance Substitutable SchemeType Type where
    apply (Sub sub) = apply (Sub (upgrade <$> sub))

null :: SubstitutionT a
null = Sub mempty

mapsTo :: Name -> a -> SubstitutionT a
mapsTo name val = Sub (Map.singleton name val)

fromList :: [(Name, a)] -> SubstitutionT a
fromList = Sub . Map.fromList

toList :: SubstitutionT a -> [(Name, a)]
toList = Map.toList . getSub

withDefault :: a -> Name -> SubstitutionT a -> a
withDefault def name = Map.findWithDefault def name . getSub

domain :: SubstitutionT a -> [Name]
domain (Sub sub) = Map.keys sub

compose :: (Substitutable a a) => SubstitutionT a -> SubstitutionT a -> SubstitutionT a
compose s1 s2 = Sub (fmap (apply s1) (getSub s2) `Map.union` getSub s1)

merge :: (Eq a) => SubstitutionT (TypeT a) -> SubstitutionT (TypeT a) -> Maybe (SubstitutionT (TypeT a))
merge s1 s2 
    | allEqual  = Just (Sub (getSub s1 `Map.union` getSub s2))
    | otherwise = Nothing
  where
    allEqual = all equal (domain s1 `intersect` domain s2)

    equal :: Name -> Bool
    equal v = let app = (`apply` tVar kTyp v) :: (Eq a) => SubstitutionT (TypeT a) -> TypeT a
               in app s1 == app s2
