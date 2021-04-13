{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
module Tau.Compiler.Substitution where

import Data.List (intersect)
import Data.Map.Strict (Map)
import Prelude hiding (null)
import Tau.Compiler.Error
import Tau.Lang
import Tau.Prog
import Tau.Tool
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Tau.Env as Env

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

instance (Substitutable t a) => Substitutable (PredicateT t) a where
    apply = fmap . apply

instance (Substitutable t a) => Substitutable (ErrorT t) a where
    apply = fmap . apply

instance (Substitutable t a) => Substitutable (ProgPattern t) a where
    apply sub = cata $ \case
        PVar    t var        -> varPat    (apply sub t) var
        PCon    t con ps     -> conPat    (apply sub t) con ps
        PLit    t prim       -> litPat    (apply sub t) prim
        PAs     t as p       -> asPat     (apply sub t) as p
        POr     t p q        -> orPat     (apply sub t) p q
        PAny    t            -> anyPat    (apply sub t)
        PTuple  t ps         -> tuplePat  (apply sub t) ps
        PList   t ps         -> listPat   (apply sub t) ps
        PRecord t row        -> recordPat (apply sub t) row

instance (Substitutable t a, Substitutable p a) => Substitutable (Binding t p) a where
    apply sub = \case
        BLet t p             -> BLet (apply sub t) (apply sub p)
        BFun t name ps       -> BFun (apply sub t) name (apply sub ps)

instance (Substitutable t a) => Substitutable (Guard (ProgExpr t)) a where
    apply sub = \case
        Guard es e           -> Guard (apply sub es) (apply sub e)

instance (Substitutable t a) => Substitutable (Clause t (ProgPattern t) (ProgExpr t)) a where
    apply sub = \case
        Clause  t gs es      -> Clause (apply sub t) (apply sub gs) (apply sub es)

instance (Substitutable t a) => Substitutable (ProgExpr t) a where
    apply sub = cata $ \case
        EVar    t var        -> varExpr    (apply sub t) var
        ECon    t con es     -> conExpr    (apply sub t) con es
        ELit    t prim       -> litExpr    (apply sub t) prim
        EApp    t es         -> appExpr    (apply sub t) es
        ELet    t bind e1 e2 -> letExpr    (apply sub t) (apply sub bind) e1 e2
        EFix    t name e1 e2 -> fixExpr    (apply sub t) name e1 e2
        ELam    t ps e       -> lamExpr    (apply sub t) (apply sub ps) e
        EIf     t e1 e2 e3   -> ifExpr     (apply sub t) e1 e2 e3
        EPat    t es cs      -> patExpr    (apply sub t) es (apply sub cs)
        EFun    t cs         -> funExpr    (apply sub t) (apply sub cs)
        EOp1    t op a       -> op1Expr    (apply sub t) (apply sub op) a
        EOp2    t op a b     -> op2Expr    (apply sub t) (apply sub op) a b
        ETuple  t es         -> tupleExpr  (apply sub t) es
        EList   t es         -> listExpr   (apply sub t) es
        ERecord t row        -> recordExpr (apply sub t) row

instance (Substitutable t a) => Substitutable (Op1 t) a where
    apply sub = \case
        ONeg   t             -> ONeg (apply sub t)
        ONot   t             -> ONot (apply sub t)

instance (Substitutable t a) => Substitutable (Op2 t) a where
    apply sub = \case
        OEq    t             -> OEq    (apply sub t)
        ONeq   t             -> ONeq   (apply sub t)
        OAnd   t             -> OAnd   (apply sub t)
        OOr    t             -> OOr    (apply sub t)
        OAdd   t             -> OAdd   (apply sub t)
        OSub   t             -> OSub   (apply sub t)
        OMul   t             -> OMul   (apply sub t)
        ODiv   t             -> ODiv   (apply sub t)
        OPow   t             -> OPow   (apply sub t)
        OMod   t             -> OMod   (apply sub t)
        OLt    t             -> OLt    (apply sub t)
        OGt    t             -> OGt    (apply sub t)
        OLte   t             -> OLte   (apply sub t)
        OGte   t             -> OGte   (apply sub t)
        OLarr  t             -> OLarr  (apply sub t)
        ORarr  t             -> ORarr  (apply sub t)
        OFpipe t             -> OFpipe (apply sub t)
        OBpipe t             -> OBpipe (apply sub t)
        OOpt   t             -> OOpt   (apply sub t)
        OStrc  t             -> OStrc  (apply sub t)
        ONdiv  t             -> ONdiv  (apply sub t)

instance Substitutable (TypeInfo e) Void where
    apply sub = \case
        TypeInfo ty ps e     -> TypeInfo (apply sub ty) (apply sub ps) e

instance (Substitutable t a) => Substitutable (Ast t) a where
    apply sub = \case
        Ast ast              -> Ast (apply sub ast)

instance Substitutable Scheme Void where
    apply sub = \case
        Forall ks ps pt      -> Forall ks ps (apply sub pt)

instance Substitutable PolyType Void where
    apply (Sub sub) = substitute (Sub (Map.map upgrade sub))

instance Substitutable TypeEnv Void where
    apply = Env.map . apply 

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

normalizer :: [(Name, Kind)] -> TypeSubstitution
normalizer vars = fromList (zipWith (\(v, k) a -> (v, tVar k a)) vars letters)

normalize :: Type -> Type
normalize ty = apply (normalizer (typeVars ty)) ty
