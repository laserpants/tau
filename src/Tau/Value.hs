{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE FlexibleContexts  #-}
module Tau.Value where

import Control.Monad.Reader
import Data.Function ((&))
import Data.Text.Prettyprint.Doc
import GHC.Show (showSpace)
import Tau.Env (Env(..))
import Tau.Expr
import Tau.Util
import qualified Data.Map.Strict as Map

-- | The environment is a mapping from variables to values.
type ValueEnv m = Env (Value m)

-- | An expression evaluates to a primitive value, a fully applied data
-- constructor, or a function closure.
data Value m
    = Value Prim                               -- ^ Literal value
    | Data Name [Value m]                      -- ^ Applied data constructor
    | Closure Name (m (Value m)) ~(ValueEnv m) -- ^ Function closure

instance Eq (Value m) where
    (==) (Value v) (Value w)     = v == w
    (==) (Data c vs) (Data d ws) = c == d && vs == ws
    (==) _ _                     = False

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
        showString "Closure <<function>>"

dataCon :: (MonadReader (ValueEnv m) m) => Name -> Int -> Value m
dataCon name 0 = Data name []
dataCon name n = Closure first val mempty
  where
    val = (ini & foldr (\fun -> asks . Closure fun)) rest
    ini = do
        Env env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)

    vars@(first:rest) = take n (nameSupply "%")

-- ============================================================================
-- == Pretty Printing
-- ============================================================================

instance Pretty (Value m) where
    pretty (Data name args) = pretty name <+> hsep (prettyArg <$> args)
    pretty value = prettyArg value

prettyArg :: Value m -> Doc a
prettyArg (Value prim)   = pretty prim
prettyArg (Data name []) = pretty name
prettyArg dat@Data{}     = parens (pretty dat)
prettyArg Closure{}      = "<<function>>"
