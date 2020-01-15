{-# LANGUAGE OverloadedStrings #-}

import Control.Monad.Reader
import Data.Text (Text)
import Tau.Core
import Tau.Core.Parser
import Tau.Eval
import Tau.Type
import Tau.Type.Unify
import Test.Hspec
import Text.Megaparsec

--

program1 :: Text
program1 = "let f = \\n -> if n == 0 then 1 else n * f (n-1) in f 5"


program2 :: Text
program2 = "\\x -> x + 1"

--

program_expr :: Text -> Expr
program_expr src = toExpr program_ast
  where
    Right program_ast = parse ast "" src


typeOf :: Text -> Type
typeOf src = apply sub t1
  where
    Right ( t1, cs ) = runInfer (infer (program_expr src))
    Right sub = runSolver cs


evald :: Text -> Value
evald src = runReader (eval (program_expr src)) mempty

--

main :: IO ()
main =
    hspec $ 
        describe "" $ do

            it "" $ 
                evald program1 `shouldBe` (Tau.Core.Int 120)

            it "" $ 
                typeOf program1 `shouldBe` tyInt

            it "" $
                typeOf program2 `shouldBe` (TyArr tyInt tyInt)
