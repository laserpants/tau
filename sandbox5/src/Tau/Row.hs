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

--data RowF e a
--    = RNil                             -- ^ Empty row
--    | RVar Name                        -- ^ Row variable
--    | RExt Name e a                    -- ^ Row extension
--
---- | Row
--type Row e = Fix (RowF e)
--
----

data RowX e = RowX (Map Name [e]) (Maybe Name) 

data RowY 
    = RowNil 
    | RowVar Name 
    | RowExt
    deriving (Show, Eq)

fooX :: RowX e -> RowY
fooX (RowX m Nothing)  | null m = RowNil
fooX (RowX m (Just r)) | null m = RowVar r
fooX _                          = RowExt

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

---- Type class instances for Row
--
--deriving instance (Show e, Show a) =>
--    Show (RowF e a)
--
--deriving instance (Eq e, Eq a) =>
--    Eq (RowF e a)
--
--deriving instance (Ord e, Ord a) =>
--    Ord (RowF e a)
--
--deriveShow1 ''RowF
--deriveEq1   ''RowF
--deriveOrd1  ''RowF
--
--deriving instance Functor     (RowF e)
--deriving instance Foldable    (RowF e)
--deriving instance Traversable (RowF e)

-- Type class instances for RowX

deriving instance (Show e) =>
    Show (RowX e)

deriving instance (Eq e) =>
    Eq (RowX e)

deriving instance (Ord e) =>
    Ord (RowX e)

deriveShow1 ''RowX
deriveEq1   ''RowX
deriveOrd1  ''RowX

deriving instance Functor     RowX
deriving instance Foldable    RowX
deriving instance Traversable RowX

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
-- Constructors
-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

---- Row
--
--rNil :: Row e 
--rNil = embed RNil
--
--rVar :: Name -> Row e 
--rVar = embed1 RVar
--
--rExt :: Name -> e -> Row e -> Row e 
--rExt = embed3 RExt

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

--type RowRep e = (Map Name [e], Maybe Name)

--rowRep :: Row e -> RowRep e
--rowRep = cata $ \case
--    RNil                     -> (mempty, Nothing)
--    RVar var                 -> (mempty, Just var)
--    RExt label e (map, leaf) -> (Map.insertWith (<>) label [e] map, leaf)
--
--repToRow :: RowRep e -> Row e
--repToRow (map, leaf) =
--    Map.foldrWithKey (flip . foldr . rExt) (maybe rNil rVar leaf) map
--
--rowPermutation :: Row e -> Name -> Maybe (Row e)
--rowPermutation row label = 
--    case Map.lookup label map of
--        Nothing     -> Nothing
--        Just (t:ts) -> Just (rExt label t (repToRow (Map.update (const (Just ts)) label map, leaf)))
--  where
--    (map, leaf) = rowRep row
--
--rowSet :: Row e -> [Row e]
--rowSet row = [fromJust (rowPermutation row label) | label <- Map.keys map]
--  where 
--    (map, _) = rowRep row
