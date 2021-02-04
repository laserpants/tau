{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
module Tau.Type.Substitution where

import Data.List (intersect)
import Data.Map.Strict (Map)
import Data.Void
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

----instance Substitutable Type Int where
----    apply (Sub sub) = undefined -- apply (Sub (upgrade <$> sub))

--instance Substitutable Type Type where
--    apply = undefined

instance Substitutable (TypeT a) (TypeT a) where
    apply sub = cata $ \case
        TVar kind var -> withDefault (tVar kind var) var sub
        TArr t1 t2    -> tArr t1 t2
        TApp t1 t2    -> tApp t1 t2
        ty            -> embed ty

instance Substitutable (TypeT Int) Type where
    apply (Sub sub) = apply (Sub (upgrade <$> sub))

--    apply sub = cata $ \case
--        TVar kind var -> withDefault (tVar kind var) var (Sub (upgrade <$> getSub sub))
--        TArr t1 t2    -> tArr t1 t2
--        TApp t1 t2    -> tApp t1 t2
--        ty            -> embed ty

--instance Substitutable (PredicateT (TypeT Int)) (TypeT Int) where
--    apply = undefined

--instance Substitutable a a where
--    apply = undefined

--foo :: SubstitutionT a -> SubstitutionT (TypeT a)
--foo = undefined

--instance Substitutable (TypeT a) a where
--    apply sub = cata $ \case
--        TVar kind var -> undefined -- withDefault (tVar kind var) var (foo sub)
--          where
--            zoom = getSub sub -- :: Map Name a
--        TArr t1 t2    -> tArr t1 t2
--        TApp t1 t2    -> tApp t1 t2
--        ty            -> embed ty


--instance Substitutable (TypeT a) a where
--    apply sub = undefined -- cata $ \case
--        TVar kind var -> (undefined :: TypeT a)
--          where
----            zoom :: Map Name a
--            zoom = getSub sub
--            --war = var :: Name
--            xxx = withDefault (undefined :: Int) var sub
--        TArr t1 t2    -> tArr t1 t2
--        TApp t1 t2    -> tApp t1 t2
--        ty            -> embed ty

--instance Substitutable Int Void where
--    apply (Sub sub) = undefined -- apply (Sub (upgrade <$> sub))
--
--instance Substitutable (PredicateT (TypeT a)) a where
--    apply = fmap . apply 
--
----instance Substitutable Scheme Int where
----    apply sub (Forall ks ps ty) = Forall ks ps (apply sub ty)
--
---- TODO : test??
--instance Substitutable Scheme Void where
--    apply sub (Forall ks ps ty) = undefined -- Forall ks ps (apply sub ty)

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
