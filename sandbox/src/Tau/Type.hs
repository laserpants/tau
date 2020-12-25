{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Type where

import Control.Comonad.Cofree
import Data.Functor.Foldable
import Data.List (nub)
import Data.Set.Monad (Set)
import Tau.Env
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

data KindF a 
    = KStar
    | KArr a a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

type Kind = Fix KindF

data TypeF a
    = TGen Int
    | TVar Kind Name 
    | TCon Kind Name 
    | TArr a a
    | TApp a a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''TypeF
deriveEq1   ''TypeF
deriveOrd1  ''TypeF

type Type = Fix TypeF

data TypeClass = TypeClass Name Type
    deriving (Show, Eq, Ord)

data Qualified t = [TypeClass] :=> t
    deriving (Show, Eq, Functor, Foldable, Traversable)

data Scheme = Forall [Kind] (Qualified Type)
    deriving (Show, Eq)

type Instance = Qualified TypeClass

type ClassInfo = ([Name], [Instance])

type ClassEnv = (Env ClassInfo, [Type])

data Assumption a = Name :>: a
    deriving (Show, Eq, Functor, Foldable, Traversable)

data TypeError
    = CannotUnify
    | CannotMatch
    | InfiniteType
    | KindMismatch
    | MergeFailed
    | ClassMismatch
    | ContextReductionFailed
    deriving (Show, Eq)

toScheme :: Type -> Scheme
toScheme ty = Forall [] ([] :=> ty1) where
    ty1 = flip cata ty $ \case
        TVar k var -> tVar k var
        TCon k con -> tCon k con
        TArr t1 t2 -> tArr t1 t2
        TApp t1 t2 -> tApp t1 t2

kindOf :: Type -> Maybe Kind
kindOf = histo $ \case
    TApp (Just t :< _) _ -> appKind (project t) 
    TCon k _             -> Just k
    TVar k _             -> Just k
    TArr{}               -> Just kStar
    _                    -> Nothing
  where
    appKind (KArr _ k) = Just k
    appKind _          = Nothing

super :: ClassEnv -> Name -> [Name]
super (info, _) name = maybe [] fst (Env.lookup name info)

instances :: ClassEnv -> Name -> [Instance]
instances (info, _) name = maybe [] snd (Env.lookup name info)

assumptionVar :: Assumption a -> Name
assumptionVar (name :>: _) = name

--findAssumption :: Name -> [Assumption a] -> Maybe a
--findAssumption _ [] = Nothing 
--findAssumption i (name :>: a:as)
--    | i == name = Just a
--    | otherwise = findAssumption i as

removeAssumption :: Name -> [Assumption a] -> [Assumption a]
removeAssumption name = filter (\a -> name /= assumptionVar a)

removeAssumptionSet :: Set Name -> [Assumption a] -> [Assumption a]
removeAssumptionSet = flip (Set.foldr removeAssumption) 

kStar :: Kind
kStar = Fix KStar

kArr :: Kind -> Kind -> Kind
kArr t1 t2 = Fix (KArr t1 t2)

tVar :: Kind -> Name -> Type
tVar k var = Fix (TVar k var)

tGen :: Int -> Type
tGen n = Fix (TGen n)

tCon :: Kind -> Name -> Type
tCon k con = Fix (TCon k con)

tArr :: Type -> Type -> Type
tArr t1 t2 = Fix (TArr t1 t2)

infixr 1 `tArr`

tApp :: Type -> Type -> Type
tApp t1 t2 = Fix (TApp t1 t2)

tUnit :: Type
tUnit = tCon kStar "Unit"

tBool :: Type
tBool = tCon kStar "Bool" 

tInt :: Type
tInt = tCon kStar "Int" 

tListCon :: Type
tListCon = tCon (kArr kStar kStar) "List"

tList :: Type -> Type
tList = tApp tListCon 
