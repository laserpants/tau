{-# LANGUAGE OverloadedStrings #-}

import Control.Exception (evaluate)
import Control.Monad.Reader
import Data.Text (Text, unpack)
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


program3 :: Text
program3 = "let f = \\x -> x in let g = f f in g ()"


program4 :: Text
program4 = "let f = \\x -> x in let g = f () in f 5"


program5 :: Text
program5 = "\\x -> x"


program6 :: Text
program6 = "3 + 3 + 3 == 3 * 3"


program7 :: Text
program7 = "5 + 3 * 2"


program8 :: Text
program8 = "2 + (-2)"


--

program_expr :: Text -> Expr
program_expr src = toExpr program_ast
  where
    Right program_ast = parse ast "" src


typeOf :: Text -> Type
typeOf src = apply sub t
  where
    Right ( t, cs ) = runInfer (infer (program_expr src))
    Right sub = runSolver cs


evald :: Text -> Value
evald src = runReader (eval (program_expr src)) mempty


main :: IO ()
main =
    hspec $ do
        describe ("Factorial of 5: " ++ unpack program1) $ do

            it "should evaluate to 120" $
                evald program1 `shouldBe` Tau.Core.Int 120

            it "should have type Int" $
                typeOf program1 `shouldBe` tyInt

        describe (unpack program2) $

            it "should have type Int -> Int" $
                typeOf program2 `shouldBe` TyArr tyInt tyInt

        describe (unpack program3) $
            it "should evaluate to ()" $
                evald program3 `shouldBe` Tau.Core.Unit

        describe (unpack program4) $

            it "should evaluate to 5" $
                evald program4 `shouldBe` Tau.Core.Int 5

        describe "Infinte type: let x = x x in 1" $

            it "should throw an exception" $
                evaluate (typeOf "let x = x x in 1") `shouldThrow` anyException

        describe ("Identity function: " ++ unpack program5) $

            it "should have type a -> a" $
                typeOf program5 `shouldBe` TyArr (TyVar "a") (TyVar "a")

        describe (unpack program6) $

            it "should evaluate to True" $
                evald program6 `shouldBe` Tau.Core.Bool True

        describe (unpack program7) $

            it "should evaluate to 11" $
                evald program7 `shouldBe` Tau.Core.Int 11

        describe (unpack program8) $

            it "should evaluate to 0" $
                evald program8 `shouldBe` Tau.Core.Int 0
