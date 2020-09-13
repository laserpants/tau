{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes     #-}
module TH where

import Data.Either (fromRight)
import Text.Megaparsec
import Data.Text (Text)
import Language.Haskell.TH (Q, Exp, runQ)
import Tau.Parser

mkExpr :: Text -> Q Exp
mkExpr input = runQ [| fromRight (error "Does not parse") (runParser expr "" input) |]

mkScheme :: Text -> Q Exp
mkScheme input = runQ [| fromRight (error "Does not parse") (runParser scheme "" input) |]

mkType :: Text -> Q Exp
mkType input = runQ [| fromRight (error "Does not parse") (runParser type_ "" input) |]

mkKind :: Text -> Q Exp
mkKind  input = runQ [| fromRight (error "Does not parse") (runParser kind "" input) |]

mkPattern :: Text -> Q Exp
mkPattern input = runQ [| fromRight (error "Does not parse") (runParser parsePattern "" input) |]
