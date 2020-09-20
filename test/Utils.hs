module Utils 
  ( module Data.Text
  , prettyString
  , typeOf
  , run
  , _expr
  , _type
  , _eval
  ) where

import Data.Maybe (fromJust)
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc (Pretty)
import Tau.Eval
import Tau.Expr
import Tau.Parser
import Tau.Solver
import Tau.Type
import Tau.Type.Inference
import Tau.Util (prettyPrint)
import Tau.Value
import Text.Megaparsec
import qualified Tau.Env.Builtin as Builtin

prettyString :: (Pretty p) => p -> String
prettyString = unpack . prettyPrint

typeOf :: Text -> Scheme
typeOf str = generalize mempty [] (apply sub ty) where
    Right (ty, sub, _) = runInferType Builtin.typeSchemes item
    Right item = parseExpr str

run :: Text -> Value Eval
run str =  _eval item where Right item = parseExpr str

_expr :: Text -> Expr
_expr str = let Right item = parseExpr str in item

_type :: Text -> Type
_type str = let Right item = parse type_ "" str in item

_eval :: Expr -> Value Eval
_eval = fromJust . flip evalExpr Builtin.values 
