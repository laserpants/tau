{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
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

data SchemeF a
    = Forall Kind [Name] a
    | Scheme Type
    deriving (Functor, Foldable, Traversable)

deriveShow  ''SchemeF
deriveEq    ''SchemeF
deriveShow1 ''SchemeF
deriveEq1   ''SchemeF

type Scheme = Fix SchemeF

----
--
--data TypeError
--    = CannotUnify
--    | CannotMatch
--    | InfiniteType
--    | KindMismatch
--    | MergeFailed
--    | ClassMismatch
--    | ContextReductionFailed
--    deriving (Show, Eq)
--
----toScheme :: Type -> Scheme
----toScheme ty = Forall [] ([] :=> ty1) where
----    ty1 = flip cata ty $ \case
----        TVar k var -> tVar k var
----        TCon k con -> tCon k con
----        TArr t1 t2 -> tArr t1 t2
----        TApp t1 t2 -> tApp t1 t2

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

tString :: Type
tString = tCon kStar "String" 

tListCon :: Type
tListCon = tCon (kArr kStar kStar) "List"

tList :: Type -> Type
tList = tApp tListCon 

sForall :: Kind -> [Name] -> Scheme -> Scheme
sForall k cs s = Fix (Forall k cs s)

sScheme :: Type -> Scheme
sScheme t = Fix (Scheme t)
