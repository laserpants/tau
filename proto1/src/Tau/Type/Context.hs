module Tau.Type.Context where

import Data.Map (Map)
import Tau.Parts
import Tau.Type (Scheme(..), Free(..), Sub)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Tau.Type as Type


newtype Context = Context (Map Var Scheme)
    deriving (Show, Eq)


instance Free Context where
    free (Context env) = 
        foldr (Set.union . free) Set.empty (Map.elems env)


extend :: Var -> Scheme -> Context -> Context 
extend name scheme (Context env) =
    Context (Map.insert name scheme env)


apply :: Sub -> Context -> Context
apply sub (Context env) = 
    Context (Map.map fun env)
  where
    fun (Forall vars tau) = Forall vars (Type.apply sub' tau)
      where
        sub' = foldr Map.delete sub vars
