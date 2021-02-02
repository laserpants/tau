{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Tau.Type.Main where

import Control.Comonad.Cofree
import Data.Void
import Tau.Type
import Tau.Util
import qualified Data.Text as Text

kTyp :: Kind
kTyp = embed KTyp

kArr :: Kind -> Kind -> Kind
kArr = embed2 KArr 

infixr 1 `kArr`

kFun :: Kind
kFun = kTyp `kArr` kTyp

tVar :: Kind -> Name -> TypeT a
tVar = embed2 TVar 

tGen :: Int -> IxType
tGen = embed1 TGen 

tCon :: Kind -> Name -> TypeT a
tCon = embed2 TCon 

tArr :: TypeT a -> TypeT a -> TypeT a
tArr = embed2 TArr 

infixr 1 `tArr`

tApp :: TypeT a -> TypeT a -> TypeT a
tApp = embed2 TApp 

--

tUnit :: Type
tUnit = tCon kTyp "Unit"

tBool :: Type
tBool = tCon kTyp "Bool" 

tInt :: Type
tInt = tCon kTyp "Int" 

tInteger :: Type
tInteger = tCon kTyp "Integer" 

tFloat :: Type
tFloat = tCon kTyp "Float" 

tString :: Type
tString = tCon kTyp "String" 

tChar :: Type
tChar = tCon kTyp "Char" 

tListCon :: Type
tListCon = tCon kFun "List"

tList :: Type -> Type
tList = tApp tListCon 

getTypeVar :: Type -> Maybe Name
getTypeVar = cata $ \case
    TVar _ v -> Just v
    _        -> Nothing

getTypeCon :: Type -> Maybe Name
getTypeCon = cata $ \case
    TCon _ c -> Just c
    _        -> Nothing

toScheme :: Type -> Scheme
toScheme = Forall [] [] . upgrade

upgrade :: Type -> IxType
upgrade = cata $ \case
    TVar k var -> tVar k var
    TCon k con -> tCon k con
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2

upgradePredicate :: Predicate -> IxPredicate
upgradePredicate (InClass name ty) = InClass name (upgrade ty)

replaceBound :: [Type] -> IxType -> Type
replaceBound ts = cata $ \case
    TGen n     -> ts !! n
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2
    TVar k var -> tVar k var
    TCon k con -> tCon k con

replaceBoundInPredicate :: [Type] -> IxPredicate -> Predicate
replaceBoundInPredicate ts (InClass name ty) = InClass name (replaceBound ts ty)

kindOf :: Type -> Maybe Kind
kindOf = histo $ \case
    TApp (Just t :< _) _ -> appKind (project t) 
    TCon k _             -> Just k
    TVar k _             -> Just k
    TArr{}               -> Just kTyp
  where
    appKind (KArr _ k) = Just k
    appKind _          = Nothing

recordConstructor :: [Name] -> TypeT a
recordConstructor names = tCon kind ("{" <> Text.intercalate "," names <> "}")
  where 
    kind = foldr kArr kTyp (replicate (length names) kTyp)
