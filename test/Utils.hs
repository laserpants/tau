module Utils 
  ( module Data.Text
  , prettyString
  , typeOf
  , run
  ) where

import Data.Maybe (fromJust)
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Eval
import Tau.Parser
import Tau.Solver
import Tau.Type
import Tau.Type.Inference
import Tau.Util (prettyPrint)
import Tau.Value
import qualified Tau.Env.Builtin as Builtin

prettyString :: (Pretty p) => p -> String
prettyString = unpack . prettyPrint

typeOf :: Text -> Scheme
typeOf str = generalize mempty [] (apply sub ty) where
    Right (ty, sub, _) = runInferType Builtin.typeSchemes item
    Right item = parseExpr str

run :: Text -> Value Eval
run str = fromJust (evalExpr item Builtin.values) where
    Right item = parseExpr str
