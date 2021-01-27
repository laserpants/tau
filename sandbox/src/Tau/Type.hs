{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Type where

import Control.Arrow (second)
import Control.Comonad.Cofree
import Data.Functor.Foldable
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Data.Set.Monad (Set)
import Tau.Env
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

-- | Base functor for kinds
data KindF a 
    = KStar  -- KType?
    | KArr a a
--    | KClass
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriveShow1 ''KindF
deriveEq1   ''KindF
deriveOrd1  ''KindF

-- | Kinds
type Kind = Fix KindF

-- | Base functor for types 
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

-- | Types
type Type = Fix TypeF

-- | Base functor for polymorphic type schemes
data SchemeF a
    = Forall Kind Name [Name] a
    | Scheme Type
    deriving (Functor, Foldable, Traversable)

deriveShow  ''SchemeF
deriveEq    ''SchemeF
deriveShow1 ''SchemeF
deriveEq1   ''SchemeF

-- | Polymorphic type schemes
type Scheme = Fix SchemeF

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

infixr 1 `kArr`

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

tInteger :: Type
tInteger = tCon kStar "Integer" 

tFloat :: Type
tFloat = tCon kStar "Float" 

tString :: Type
tString = tCon kStar "String" 

tChar :: Type
tChar = tCon kStar "Char" 

tListCon :: Type
tListCon = tCon (kArr kStar kStar) "List"

tList :: Type -> Type
tList = tApp tListCon 

sForall :: Kind -> Name -> [Name] -> Scheme -> Scheme
sForall k n cs s = Fix (Forall k n cs s)

sScheme :: Type -> Scheme
sScheme t = Fix (Scheme t)


