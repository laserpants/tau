{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
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
import Data.Tuple.Extra (first)
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
groups qs = cs:gs
  where
    (cs, gs) = foldr (uncurry arrange) (ConEqs [], []) qs

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

-- | A simple pattern is either a variable or a constructor where all the
-- subpatterns are variables.
isSimple :: Pattern -> Bool
isSimple = fun . unfix where
    fun AnyP        = True
    fun (VarP _)    = True
    fun (ConP _ ps) = all isSimple ps
    fun _           = False

allSimple :: Expr -> Bool
allSimple = cata alg where
    alg :: Algebra ExprF Bool
    alg = \case
        LamS _ expr ->
            expr

        AppS exprs ->
            and exprs

        LetS _ expr body ->
            expr && body

        IfS cond true false ->
            cond && true && false

        OpS (AddS a b) -> a && b
        OpS (SubS a b) -> a && b
        OpS (MulS a b) -> a && b
        OpS (EqS a b) -> a && b
        OpS (LtS a b) -> a && b
        OpS (GtS a b) -> a && b
        OpS (NegS a) -> a
        OpS (NotS a) -> a

        AnnS expr _ ->
            expr

        CaseS expr clss ->
            expr && and (snd <$> clss)
                 && and (isSimple . fst <$> clss)

        _ ->
            True

compileAll :: Expr -> Expr
compileAll = cata alg where
    alg :: Algebra ExprF Expr
    alg = \case
        CaseS expr clss ->
            runPatternCompile (compile [expr] (first (:[]) <$> clss))

        expr ->
            Fix expr
