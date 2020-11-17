{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Type where

import Control.Comonad.Cofree
import Data.Functor.Foldable
import Data.List (nub)
import Tau.Env
import Tau.Util
import qualified Tau.Env as Env

data KindF a 
    = Star
    | KArr a a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

type Kind = Fix KindF

data TypeF a
    = TBound Int
    | TVar Kind Name 
    | TCon Kind Name 
    | TArr a a
    | TApp a a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

type Type = Fix TypeF

data TyClass = TyClass Name Type
    deriving (Show, Eq, Ord)

data Qualified t = [TyClass] :=> t
    deriving (Show, Eq, Functor, Foldable, Traversable)

data Scheme = Forall [Kind] (Qualified Type)
    deriving (Show, Eq)

type Instance = Qualified TyClass

type ClassInfo = ([Name], [Instance])

type ClassEnv = (Env ClassInfo, [Type])

data Assumption a = Name :>: a
    deriving (Show, Eq, Functor, Foldable, Traversable)

star :: Kind
star = Fix Star

karr :: Kind -> Kind -> Kind
karr a1 a2 = Fix (KArr a1 a2)

tvar :: Kind -> Name -> Type
tvar a1 a2 = Fix (TVar a1 a2)

tbound :: Int -> Type
tbound a1 = Fix (TBound a1)

tcon :: Kind -> Name -> Type
tcon a1 a2 = Fix (TCon a1 a2)

tarr :: Type -> Type -> Type
tarr a1 a2 = Fix (TArr a1 a2)

infixr 1 `tarr`

tapp :: Type -> Type -> Type
tapp a1 a2 = Fix (TApp a1 a2)

tUnit :: Type
tUnit = tcon star "Unit"

tBool :: Type
tBool = tcon star "Bool" 

tInt :: Type
tInt = tcon star "Int" 

tListCon :: Type
tListCon = tcon (karr star star) "List"

tList :: Type -> Type
tList = tapp tListCon 

toScheme :: Type -> Scheme
toScheme ty = Forall [] ([] :=> ty) where
    ty = flip cata ty $ \case
        TVar k name -> tvar k name
        TCon k name -> tcon k name
        TArr t1 t2  -> tarr t1 t2
        TApp t1 t2  -> tapp t1 t2

kindOf :: Type -> Maybe Kind
kindOf = histo $ \case
    TApp (Just (Fix (KArr _ k)) :< _) _ -> Just k
    TCon k _ -> Just k
    TVar k _ -> Just k
    TArr{}   -> Just star
    _        -> Nothing

super :: ClassEnv -> Name -> [Name]
super (info, _) name = maybe [] fst (Env.lookup name info)

instances :: ClassEnv -> Name -> [Instance]
instances (info, _) name = maybe [] snd (Env.lookup name info)

getVar :: Assumption a -> Name
getVar (name :>: _) = name

findAssumption :: Name -> [Assumption a] -> Maybe a
findAssumption _ [] = Nothing 
findAssumption i (name :>: a:as) = 
    if i == name 
        then Just a 
        else findAssumption i as

removeAssumption :: Name -> [Assumption a] -> [Assumption a]
removeAssumption name = filter (\a -> name /= getVar a)

removeAssumptionSet :: [Assumption a] -> [Assumption a] -> [Assumption a]
removeAssumptionSet ts = flip (foldr removeAssumption) (nub (getVar <$> ts))
