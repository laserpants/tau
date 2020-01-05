module Tau.Type.Context where

import Data.Map (Map)
import Tau.Type (Scheme(..), Free(..), Substitutable(..), Sub)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Tau.Type as Type


newtype Context = Context (Map Var Scheme)
    deriving (Show, Eq)


instance Free Context where
    free (Context env) = foldr (Set.union . free) Set.empty (Map.elems env)


empty :: Context
empty = Context Map.empty


extend :: Var -> Scheme -> Context -> Context 
extend name scheme (Context env) =
    Context (Map.insert name scheme env)


remove :: Var -> Context -> Context
remove name (Context env) = 
    Context (Map.delete name env)


instance Substitutable Context where
    substitute sub (Context env) = Context (Map.map fun env)
      where
        fun (Forall vars tau) = Forall vars (substitute (foldr Map.delete sub vars) tau)
