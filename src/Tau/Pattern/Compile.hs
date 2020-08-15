{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StrictData                 #-}
module Tau.Pattern.Compile where

import Control.Monad (replicateM)
import Control.Monad.Identity
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Functor.Foldable
import Data.List.Extra (groupSortOn)
import Data.Text (pack)
import Tau.Ast
import Tau.Core
import Tau.Pattern
import Tau.Prim
import Tau.Substitution
import Tau.Type

type Equation = ([Pattern], Expr)

data ConHead = ConHead
    { conName  :: Name
    , conArity :: Int
    , conPttns :: [Pattern]
    , conExpr  :: Expr
    } deriving (Show, Eq)

data VarHead = VarHead
    { varName  :: Maybe Name
    , varPttns :: [Pattern]
    , varExpr  :: Expr
    } deriving (Show, Eq)

data LitHead = LitHead
    { litPrim  :: Prim
    , litPttns :: [Pattern]
    , litExpr  :: Expr
    } deriving (Show, Eq)

data EqGroup
    = ConEqs [ConHead]
    | VarEqs [VarHead]
    | LitEqs [LitHead]
    deriving (Show, Eq)

groups :: [Equation] -> [EqGroup]
groups qs = let (cs, gs) = foldr (uncurry arrange) (ConEqs [], []) qs in cs:gs
  where
    arrange (Fix (ConP name qs):ps) expr =
        let c = ConHead { conName  = name
                        , conArity = length qs
                        , conPttns = qs <> ps
                        , conExpr  = expr }
         in \case
            (ConEqs cs, gs) -> (ConEqs (c:cs), gs)
            (g, gs)         -> (ConEqs [c], g:gs)

    arrange (Fix (VarP name):ps) expr =
        let c = VarHead { varName  = Just name
                        , varPttns = ps
                        , varExpr  = expr }
         in \case
            (VarEqs cs, gs) -> (VarEqs (c:cs), gs)
            (g, gs)         -> (VarEqs [c], g:gs)

    arrange (Fix AnyP:ps) expr =
        let c = VarHead { varName  = Nothing
                        , varPttns = ps
                        , varExpr  = expr }
         in \case
            (VarEqs cs, gs) -> (VarEqs (c:cs), gs)
            (g, gs)         -> (VarEqs [c], g:gs)

    arrange (Fix (LitP prim):ps) expr =
        let c = LitHead { litPrim  = prim
                        , litPttns = ps
                        , litExpr  = expr }
         in \case
            (LitEqs cs, gs) -> (LitEqs (c:cs), gs)
            (g, gs)         -> (LitEqs [c], g:gs)

data ConGroup = ConGroup
    { name      :: Name
    , arity     :: Int
    , equations :: [Equation]
    } deriving (Show)

conGroups :: [ConHead] -> [ConGroup]
conGroups qs =
    makeGroup <$> groupSortOn (\ConHead{..} -> (conName, conArity)) qs
  where
    makeGroup cs@(ConHead{..}:_) = ConGroup
      { name      = conName
      , arity     = conArity
      , equations = (\ConHead{..} -> (conPttns, conExpr)) <$> cs }

type PatternCompileTStack m a = SupplyT Name m a

newtype PatternCompileT m a = PatternCompileT (PatternCompileTStack m a)
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadSupply Name )

runPatternCompileT :: Monad m => PatternCompileT m a -> m a
runPatternCompileT (PatternCompileT a) = evalSupplyT a (pfxed <$> [1..]) where
    pfxed count = ":" <> pack (show count)

type PatternCompile = PatternCompileT Identity

runPatternCompile :: PatternCompile a -> a
runPatternCompile = runIdentity . runPatternCompileT

compile :: MonadSupply Name m => [Expr] -> [Equation] -> m Expr
compile = matchDefault errS

matchDefault :: MonadSupply Name m => Expr -> [Expr] -> [Equation] -> m Expr
matchDefault _ [] [([], expr)] = pure expr
matchDefault def (u:us) qs = foldrM (flip run) def (groups qs) where
    run :: MonadSupply Name m => Expr -> EqGroup -> m Expr
    run def = \case
        ConEqs eqs -> do
            css <- traverse groupClause (conGroups eqs)
            pure $ case css <> [(anyP, def) | errS /= def] of
                [] -> def
                css' -> caseS u css'
          where
            groupClause :: MonadSupply Name m => ConGroup -> m (Pattern, Expr)
            groupClause ConGroup{..} = do
                vs <- replicateM arity supply
                expr <- matchDefault def ((varS <$> vs) <> us) equations
                pure (conP name (varP <$> vs), expr)

        VarEqs eqs ->
            matchDefault def us (fun <$> eqs) where
                fun VarHead{..} =
                    ( varPttns
                    , case varName of
                          Nothing   -> varExpr
                          Just name -> substitute name u varExpr )

        LitEqs eqs ->
            foldrM fun def eqs where
                fun LitHead{..} false = do
                    true <- matchDefault def us [(litPttns, litExpr)]
                    pure (ifS (eqS u (litS litPrim)) true false)
