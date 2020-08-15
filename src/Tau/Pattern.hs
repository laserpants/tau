{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE TemplateHaskell            #-}
module Tau.Pattern where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Eq.Deriving
import Data.Functor.Foldable
import Data.Map.Strict (Map)
import Data.Set.Monad (Set)
import Tau.Prim
import Tau.Util
import Text.Show.Deriving
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set

data PatternF a
    = VarP Name              -- ^ Variable pattern
    | ConP Name [a]          -- ^ Constuctor pattern
    | LitP Prim              -- ^ Literal pattern
    | AnyP                   -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Pattern = Fix PatternF

-- VarP constructor
varP :: Name -> Pattern
varP = Fix . VarP

-- ConP constructor
conP :: Name -> [Pattern] -> Pattern
conP a = Fix . ConP a

-- LitP constructor
litP :: Prim -> Pattern
litP = Fix . LitP

-- AnyP constructor
anyP :: Pattern
anyP = Fix AnyP

specialized :: Name -> Int -> [[Pattern]] -> [[Pattern]]
specialized name a = concatMap fun where
    fun (p:ps) =
        case unfix p of
            ConP name' ps0
                | name' == name -> [ps0 <> ps]
                | otherwise     -> []

            _ ->
                [replicate a (Fix AnyP) <> ps]

defaultMatrix :: [[Pattern]] -> [[Pattern]]
defaultMatrix = concatMap fun where
    fun (p:ps) =
        case unfix p of
            ConP{} -> []
            _      -> [ps]

data PatternCheckError
    = ImplementationError
    deriving (Show, Eq)

type Lookup = Map Name (Set Name)

lookupFromList :: [(Name, [Name])] -> Lookup
lookupFromList = Map.fromList . fmap (fmap Set.fromList)

type PatternCheckTStack m a = ReaderT Lookup (ExceptT PatternCheckError m) a

newtype PatternCheckT m a = PatternCheckT (PatternCheckTStack m a) deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader Lookup
    , MonadError PatternCheckError )

runPatternCheckT :: PatternCheckT m a -> Lookup -> m (Either PatternCheckError a)
runPatternCheckT (PatternCheckT a) = runExceptT . runReaderT a

type PatternCheck = PatternCheckT Identity

runPatternCheck :: PatternCheck a -> Lookup -> Either PatternCheckError a
runPatternCheck a = runIdentity . runPatternCheckT a

headCons :: Monad m => [[Pattern]] -> PatternCheckT m [(Name, Int)]
headCons = fmap concat . traverse fun where
    fun []                     = throwError ImplementationError
    fun (Fix (ConP name rs):_) = pure [(name, length rs)]
    fun _                      = pure []

useful :: Monad m => [[Pattern]] -> [Pattern] -> PatternCheckT m Bool
useful [] qs = pure True        -- zero rows (0x0 matrix)
useful pss@(ps:_) qs =
    case (qs, length ps) of
        (_, 0) -> pure False    -- 1 or more rows but zero cols

        ([], _) ->
            throwError ImplementationError

        (Fix (ConP name rs):_, n) ->
            let special = specialized name (length rs)
             in useful (special pss) (head (special [qs]))

        (_:qs1, n) -> do
            constrs <- headCons pss
            isComplete <- complete (fst <$> constrs)
            if isComplete
                then constrs |> anyM (\con ->
                    let special = uncurry specialized con
                     in useful (special pss) (head (special [qs])))
                else useful (defaultMatrix pss) qs1
  where
    complete [] = pure False
    complete names@(name:_) = do
        lookup <- ask
        pure (Map.findWithDefault mempty name lookup == Set.fromList names)

exhaustive :: Monad m => [Pattern] -> PatternCheckT m Bool
exhaustive ps = not <$> useful ((:[]) <$> ps) [Fix AnyP]

$(deriveShow1 ''PatternF)
$(deriveEq1   ''PatternF)
