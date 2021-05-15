{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Compiler.Pipeline where

import Tau.Lang
import Tau.Tool

data SimplifiedClause t p a = SimplifiedClause t [p] (Guard a) 

deriving instance (Show t, Show p, Show a) => 
    Show (SimplifiedClause t p a)

deriving instance (Eq t, Eq p, Eq a) => 
    Eq (SimplifiedClause t p a)

deriving instance (Ord t, Ord p, Ord a) => 
    Ord (SimplifiedClause t p a)

deriving instance Functor (SimplifiedClause t p)
deriving instance Foldable (SimplifiedClause t p)
deriving instance Traversable (SimplifiedClause t p)

deriveShow1 ''SimplifiedClause
deriveEq1   ''SimplifiedClause
deriveOrd1  ''SimplifiedClause
