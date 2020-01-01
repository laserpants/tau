module Main where

import Control.Monad.Reader
import Debug.Trace
import Tau.Eval
import Tau.Parts
import Tau.Syntax
import Tau.Type
import Tau.Type.Context (Context(..))
import Tau.Type.Unify


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

expr1Type = runInfer (infer (Context mempty) expr1)

expr2Type = runInfer (infer (Context mempty) expr2)

main :: IO ()
main = do
   print (runReader (eval fact5) mempty, 120)
   print (runReader (eval expr1) mempty)
   print (runReader (eval expr2) mempty, 4)
   print (runReader (eval expr3) mempty, 5)
   print (runReader (eval expr4) mempty, 4)
   print (snd expr1Type)
   print (snd expr2Type)
