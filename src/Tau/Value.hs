{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Value where

import Control.Monad.Reader
import Data.Map.Strict (Map)
import Data.Text (pack)
import GHC.Show (showSpace)
import Tau.Ast
import Tau.Core
import Tau.Prim
import qualified Data.Map.Strict as Map

-- | The environment is a mapping from variables to values.
type Env m = Map Name (Value m)

-- | An expression evaluates to a primitive value, a fully applied data
-- constructor, or a function closure.
data Value m
    = Value Prim                           -- ^ Literal value
    | Data Name [Value m]                  -- ^ Applied data constructor
    | Closure Name (m (Value m)) ~(Env m)  -- ^ Function closure

instance Eq (Value m) where
    Value v   == Value w   = v == w
    Data c vs == Data d ws = c == d && vs == ws
    _ == _                 = False

instance Show (Value m) where
    showsPrec p (Value val) =
        showParen (p >= 11)
            $ showString "Value"
            . showSpace
            . showsPrec 11 val
    showsPrec p (Data name vals) =
        showParen (p >= 11)
            $ showString "Data"
            . showSpace
            . showsPrec 11 name
            . showSpace
            . showsPrec 11 vals
    showsPrec _ Closure{} =
        showString "<<function>>"

dataCon :: (MonadReader (Env m) m) => Name -> Int -> Value m
dataCon name 0 = Data name []
dataCon name n = Closure (varName 1) val mempty
  where
    val = tail vars
        $> init
        |> foldr (\name -> asks . Closure name)

    init = do
        env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)

    vars = varName <$> [1..n]
    varName n = "%" <> pack (show n)
