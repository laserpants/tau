{-# LANGUAGE OverloadedStrings #-}
module TestUtils where
--  ( module Debug.Trace
--  , describe
--  , it
--  , _a
--  , _b
--  , _c
--  , prettyText
--  ) where

import Control.Monad.Except
import Control.Monad.Supply
import Data.Maybe (fromJust)
import Data.Text (Text, unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Debug.Trace
import Tau.Util
import Tau.Type
import Test.Hspec hiding (describe, it) 
import qualified Test.Hspec as Hspec

describe :: Text -> SpecWith () -> SpecWith ()
describe = Hspec.describe . unpack

it :: (Example a) => Text -> a -> SpecWith (Arg a)
it = Hspec.it . unpack

_a :: Type
_a = tVar kTyp "a"

_b :: Type
_b = tVar kTyp "b"

_c :: Type
_c = tVar kTyp "c"

runUnify :: SupplyT Name (ExceptT err Maybe) a -> Either err a
runUnify e = fromJust (runExceptT (evalSupplyT e (numSupply "")))


