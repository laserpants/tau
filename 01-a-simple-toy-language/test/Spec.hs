{-# LANGUAGE OverloadedStrings #-}

import Control.Monad.Reader
import Data.Text (Text)
import Tau.Core
import Tau.Eval
import Tau.Core.Parser
import Test.Hspec
import Text.Megaparsec


program1 :: Text
program1 = "let f = \\n -> if n == 0 then 1 else n * f (n-1) in f 5"


program1_ast :: Ast
Right program1_ast = parse ast "" program1


program1_expr :: Expr
program1_expr = toExpr program1_ast


program1_val :: Value
program1_val = runReader (eval program1_expr) mempty


main :: IO ()
main =
    hspec $ do
        describe "" $ do
            it "" $ do
                program1_val `shouldBe` (Tau.Core.Int 120)
