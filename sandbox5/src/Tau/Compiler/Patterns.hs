module Tau.Compiler.Patterns where

import Tau.Lang
import Tau.Tooling

useful 
  :: (Monad m) 
  => [[Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9]] 
  -> [Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9] 
  -> m Bool
useful [] _   = pure True   -- Zero rows (0x0 matrix)
useful (p1:_) qs 
    | null p1 = pure False  -- One or more rows but no columns
    | null qs = error "Implementation error (useful)"
useful pss (q:qs) =
    undefined
