module Tau.Type.Context where

import Data.Map (Map)
import Tau.Type (Scheme(..), Free(..), Substitutable(..), Sub)
import Tau.Util
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Tau.Type as Type


-- | The type context (environment) is a mapping from variables to type schemes.
--
newtype Context = Context (Map Name Scheme)
    deriving (Show, Eq)


instance Free Context where
    free (Context env) = foldr (Set.union . free) Set.empty (Map.elems env)


-- | The empty type context
--
empty :: Context
empty = Context Map.empty


extend :: Name -> Scheme -> Context -> Context 
extend name scheme (Context env) =
    Context (Map.insert name scheme env)


-- | Remove a name from the type context.
--
remove :: Name -> Context -> Context
remove name (Context env) =
    Context (Map.delete name env)


instance Substitutable Context where
    apply sub (Context env) = Context (Map.map fun env)
      where
        fun (Forall vars tau) = Forall vars (apply (foldr Map.delete sub vars) tau)
