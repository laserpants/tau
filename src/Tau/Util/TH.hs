{-# LANGUAGE TemplateHaskell #-}
module Tau.Util.TH where

import Data.Either (fromRight)
import Data.Text (Text)
import Language.Haskell.TH (Q, Exp, runQ)
import Tau.Expr
import Tau.Parser
import Tau.Type
import Text.Megaparsec

parseWithDefault :: a -> Parser a -> Text -> a
parseWithDefault def parser = fromRight def . runParser parser ""

parseExpr :: Text -> Q Exp
parseExpr input = runQ [| parseWithDefault errS expr input |]

parseScheme :: Text -> Q Exp
parseScheme input = runQ [| parseWithDefault (Forall [] [] (conT "?")) scheme input |]

parseType :: Text -> Q Exp
parseType input = runQ [| parseWithDefault (conT "?") type_ input |]

parseKind :: Text -> Q Exp
parseKind  input = runQ [| parseWithDefault (varK "?") kind input |]

parsePattern :: Text -> Q Exp
parsePattern input = runQ [| parseWithDefault (varP "?") pattern_ input |]
