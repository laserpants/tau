{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Row where

import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Tau.Tool
import qualified Data.Map.Strict as Map

-- | Row
data Row e = Row (Map Name [e]) (Maybe Name) 

data RowType 
    = RNil 
    | RVar Name 
    | RExt
    deriving (Show, Eq)

rowType :: Row e -> RowType
rowType (Row m Nothing)  | null m = RNil
rowType (Row m (Just r)) | null m = RVar r
rowType _                         = RExt

concatRow :: Row e -> [e]
concatRow (Row m _) = Map.foldr (<>) mempty m

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

-- Type class instances for Row

deriving instance (Show e) =>
    Show (Row e)

deriving instance (Eq e) =>
    Eq (Row e)

deriving instance (Ord e) =>
    Ord (Row e)

deriveShow1 ''Row
deriveEq1   ''Row
deriveOrd1  ''Row

deriving instance Functor     Row
deriving instance Foldable    Row
deriving instance Traversable Row

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Constructors
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

rNil :: Row e 
rNil = Row mempty Nothing

rVar :: Name -> Row e 
rVar var = Row mempty (Just var)

rExt :: Name -> e -> Row e -> Row e 
rExt var e (Row map r) = Row (Map.insertWith (<>) var [e] map) r
