{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Lang.Type.Row where

import Data.Map (Map)
import Data.Maybe (fromJust)
import Tau.Lang.Type
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Text as Text

data RowF g a
    = RNil 
    | RVar Name 
    | RExt Name (TypeT g) a
    deriving (Show, Eq, Functor, Foldable)

deriveShow1 ''RowF
deriveEq1   ''RowF

type Row g = Fix (RowF g)

rNil :: Row g
rNil = embed RNil

rVar :: Name -> Row g
rVar = embed1 RVar

rExt :: Name -> TypeT g -> Row g -> Row g
rExt = embed3 RExt

unfoldRow :: TypeT g -> Row g
unfoldRow = para $ \case
    TApp (t, _) (_, row) -> rExt (fieldName t) (fieldType t) row
    TVar _ var           -> rVar var
    _                    -> rNil
  where
    fieldName :: TypeT g -> Name
    fieldName = cata $ \case
        TCon _ a -> Text.tail (Text.init a)
        TApp a _ -> a

    fieldType :: TypeT g -> TypeT g
    fieldType = cata $ \case
        TApp _ a -> a
        t        -> embed t

foldRow :: Row g -> TypeT g
foldRow = cata $ \case
    RNil              -> tEmptyRow
    RVar var          -> tVar kRow var
    RExt label ty row -> tRowExtend label ty row

rowRepresentation :: Row g -> (Map Name [TypeT g], Maybe Name)
rowRepresentation = cata $ \case
    RNil                     -> (mempty, Nothing)
    RVar var                 -> (mempty, Just var)
    RExt label ty (map, fin) -> (Map.insertWith (<>) label [ty] map, fin)

repToRow :: (Map Name [TypeT g], Maybe Name) -> Row g
repToRow (map, fin) =
    Map.foldrWithKey (flip . foldr . rExt) (maybe rNil rVar fin) map

rowPermutation :: Name -> Row g -> Maybe (Row g)
rowPermutation label row = 
    case Map.lookup label map of
        Nothing     -> Nothing
        Just (t:ts) -> Just (rExt label t (repToRow (Map.update (const (Just ts)) label map, fin)))
  where
    (map, fin) = rowRepresentation row

rowSet :: Row g -> [Row g]
rowSet row = [fromJust (rowPermutation label row) | label <- Map.keys rep]
  where 
    (rep, _) = rowRepresentation row

tRowCon :: Name -> TypeT a
tRowCon label = tCon (kTyp `kArr` kRow `kArr` kRow) ("{" <> label <> "}")

tRowExtend :: Name -> TypeT a -> TypeT a -> TypeT a 
tRowExtend label ty = tApp (tApp (tRowCon label) ty) 

tEmptyRow :: TypeT a
tEmptyRow = tCon kRow "{}"
