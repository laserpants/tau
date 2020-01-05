{-# LANGUAGE RankNTypes #-}
module Main where

import Control.Monad.Reader
import Debug.Trace
import Tau.Core
import Tau.Eval
import Tau.Type
import Tau.Type.Context (Context(..))
import Tau.Type.Unify
import Tau.Util


expr1 = Lam "x" (Op Add (Var "x") (Lit (Int 1)))

expr2 = App expr1 (Lit (Int 3))

expr3 = -- let x = 4 in let x = 5 in x
    Let "x" (Lit (Int 4)) (Let "x" (Lit (Int 5)) (Var "x"))

expr4 = 
    Let "x" (Lit (Int 4)) (Let "y" (Lit (Int 5)) (Var "x"))

fact =
    Fix (Lam "f"
        (Lam "n"
            (If (Op Eq (Lit (Int 0)) (Var "n"))
                (Lit (Int 1))
                (Op Mul (Var "n") (App (Var "f") (Op Sub (Var "n") (Lit (Int 1))))))
        )
    )

fact5 = App fact (Lit (Int 5))

expr1Type = runInfer (infer expr1)

expr2Type = runInfer (infer expr2)

expr6 = Lam "x" (Lam "y" (Lam "z" (Op Add (Op Add (Var "x") (Var "y")) (Var "z"))))

expr6Type = runInfer (infer expr6)


fun :: (forall a.a -> Int) -> ( Int, Int )
fun g = ( g True, g 3 )


main :: IO ()
main = do
   print (runReader (eval fact5) mempty, 120)
   print (runReader (eval expr1) mempty)
   print (runReader (eval expr2) mempty, 4)
   print (runReader (eval expr3) mempty, 5)
   print (runReader (eval expr4) mempty, 4)
   print expr1Type
   print expr2Type
