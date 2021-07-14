{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Compiler.Pipeline where

import Tau.Lang
import Tau.Util

-- BasicClause?
data SimplifiedClause t p a = SimplifiedClause t [p] (Guard a) 

-- BasicPattern?
data SimplifiedPattern t = SCon t Name [Name]

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

deriving instance (Show t, Show p, Show a) => 
    Show (SimplifiedClause t p a)

deriving instance (Eq t, Eq p, Eq a) => 
    Eq (SimplifiedClause t p a)

deriving instance (Ord t, Ord p, Ord a) => 
    Ord (SimplifiedClause t p a)

deriving instance Functor     (SimplifiedClause t p)
deriving instance Foldable    (SimplifiedClause t p)
deriving instance Traversable (SimplifiedClause t p)

deriveShow1 ''SimplifiedClause
deriveEq1   ''SimplifiedClause
deriveOrd1  ''SimplifiedClause

deriving instance (Show t) => Show (SimplifiedPattern t)
deriving instance (Eq   t) => Eq   (SimplifiedPattern t)
