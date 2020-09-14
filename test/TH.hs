{-# LANGUAGE TemplateHaskell #-}
module TH where

import Data.Either (fromRight)
import Text.Megaparsec
import Data.Text (Text)
import Language.Haskell.TH (Q, Exp, runQ)
import Tau.Parser

forceParser :: Parser a -> Text -> a
forceParser parser = fromRight (error "Does not parse") . runParser parser ""

mkExpr :: Text -> Q Exp
mkExpr input = runQ [| forceParser expr input |]

mkScheme :: Text -> Q Exp
mkScheme input = runQ [| forceParser scheme input |]

mkType :: Text -> Q Exp
mkType input = runQ [| forceParser type_ input |]

mkKind :: Text -> Q Exp
mkKind  input = runQ [| forceParser kind input |]

mkPattern :: Text -> Q Exp
mkPattern input = runQ [| forceParser parsePattern input |]
