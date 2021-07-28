{-# LANGUAGE LambdaCase            #-}
module Main where
 
import Data.Functor.Foldable
import Tau.Misc

main :: IO ()
main = print "done"

tagTree
  :: (Monad m)
  => ProgExpr t u 
  -> m (ProgExpr Name u)
tagTree = cata $ \case

    EVar t var -> 
        pure (varExpr "a0" var)

--    ECon    t2  Name [a]             
--    ELit    t3  Prim                 
--    EApp    t4  [a]                  
--    EFix    t5  Name a a             
--    ELam    t6  e1 a                 
--    EIf     t7  a a a                
--    EPat    t8  a [e2 a]             
--    ELet    t9  e3 a a               
--    EFun    t10 [e4 a]               
--    EOp1    t11 (Op1 t11) a          
--    EOp2    t12 (Op2 t12) a a        
--    ETuple  t13 [a]                  
--    EList   t14 [a]                  
--    ERow    t15 Name a a             
--    EHole   t16                      

--    EAnn t a ->
--        undefined -- pure (annExpr t a)
