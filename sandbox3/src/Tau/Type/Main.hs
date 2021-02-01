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

tVar :: Kind -> Name -> Type a
tVar = embed2 TVar 

tGen :: Int -> Type Int
tGen = embed1 TGen 

tCon :: Kind -> Name -> Type a
tCon = embed2 TCon 

tArr :: Type a -> Type a -> Type a
tArr = embed2 TArr 

infixr 1 `tArr`

tApp :: Type a -> Type a -> Type a
tApp = embed2 TApp 

--

tUnit :: Type Void
tUnit = tCon kTyp "Unit"

tBool :: Type Void
tBool = tCon kTyp "Bool" 

tInt :: Type Void
tInt = tCon kTyp "Int" 

tInteger :: Type Void
tInteger = tCon kTyp "Integer" 

tFloat :: Type Void
tFloat = tCon kTyp "Float" 

tString :: Type Void
tString = tCon kTyp "String" 

tChar :: Type Void
tChar = tCon kTyp "Char" 

tListCon :: Type Void
tListCon = tCon kFun "List"

tList :: Type Void -> Type Void
tList = tApp tListCon 

forall :: Kind -> Name -> [Name] -> Scheme -> Scheme
forall = embed4 Forall 

scheme :: Type Int -> Scheme
scheme = embed1 Scheme 

scheme_ :: Type Void -> Scheme
scheme_ = embed1 Scheme . upgrade

upgrade :: Type Void -> Type Int
upgrade = cata $ \case
    TVar k var -> tVar k var
    TCon k con -> tCon k con
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2

downgrade :: Type Int -> Type Void
downgrade = cata $ \case
    TVar k var -> tVar k var
    TCon k con -> tCon k con
    TArr t1 t2 -> tArr t1 t2
    TApp t1 t2 -> tApp t1 t2
    _          -> error "Implementation error"

kindOf :: Type Void -> Maybe Kind
kindOf = histo $ \case
    TApp (Just t :< _) _ -> appKind (project t) 
    TCon k _             -> Just k
    TVar k _             -> Just k
    TArr{}               -> Just kTyp
  where
    appKind (KArr _ k) = Just k
    appKind _          = Nothing

recordConstructor :: [Name] -> Type Void
recordConstructor names = tCon kind ("{" <> Text.intercalate "," names <> "}")
  where 
    kind = foldr kArr kTyp (replicate (length names) kTyp)
