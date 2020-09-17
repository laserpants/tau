{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
module Tau.Patterns where

import Control.Monad.Extra (anyM, (&&^))
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Supply
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.Maybe (fromJust)
import Data.List.Extra (groupSortOn)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (first)
import Tau.Env
import Tau.Expr
import Tau.Type
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

specialized :: Name -> Int -> [[Pattern]] -> [[Pattern]]
specialized name a = concatMap $ \(p:ps) ->
    case unfix p of
        ConP name' ps'
            | name' == name -> [ps' <> ps]
            | otherwise     -> []

        _ ->
            [replicate a anyP <> ps]

defaultMatrix :: [[Pattern]] -> [[Pattern]]
defaultMatrix = concatMap $ \(p:ps) ->
    case unfix p of
        ConP{} -> []
        LitP{} -> []
        _      -> [ps]

type ConstructorEnv = Env (Set Name)

constructorEnv :: [(Name, [Name])] -> ConstructorEnv
constructorEnv = Env.fromList . fmap (fmap Set.fromList)

headCons :: (Monad m) => [[Pattern]] -> m [(Name, Int)]
headCons = fmap concat . traverse fun where
    fun [] = error "Implementation error in pattern anomalies check"
    fun ps = pure $ case unfix (head ps) of
        LitP lit     -> [(prim lit, 0)]
        ConP name rs -> [(name, length rs)]
        _            -> []
    prim (Bool True)  = "$True"
    prim (Bool False) = "$False"
    prim Unit         = "$()"
    prim Int{}        = "$Int"
    prim Integer{}    = "$Integer"
    prim Float{}      = "$Float"
    prim Char{}       = "$Char"
    prim String{}     = "$String"

useful :: (MonadReader ConstructorEnv m) => [[Pattern]] -> [Pattern] -> m Bool
useful [] _ = pure True         -- zero rows (0x0 matrix)
useful px@(ps:_) qs =
    case (qs, length ps) of
        (_, 0) -> pure False    -- one or more rows but no columns

        ([], _) ->
            error "Implementation error in pattern anomalies check"

        (Fix (ConP name rs):_, _) ->
            let special = specialized name (length rs)
             in useful (special px) (head (special [qs]))

        (_:qs1, _) -> do
            cs <- headCons px
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\con ->
                    let special = uncurry specialized con
                     in useful (special px) (head (special [qs])))
                else useful (defaultMatrix px) qs1
  where
    complete [] = pure False
    complete names@(name:_) = do
        defined <- ask
        let constructors = defined `Env.union` builtIn
        pure (Env.findWithDefaultEmpty name constructors == Set.fromList names)

    builtIn = constructorEnv
        [ ("$True",     ["$True", "$False"])
        , ("$False",    ["$True", "$False"])
        , ("$()",       ["$()"])
        , ("$Int",      [])
        , ("$Integer",  [])
        , ("$Float",    [])
        , ("$Char",     [])
        , ("$String",   [])
        ]

exhaustive :: (MonadReader ConstructorEnv m) => [Pattern] -> m Bool
exhaustive ps = not <$> useful ((:[]) <$> ps) [anyP]

checkPatterns :: (Monad m) => ([MatchClause Bool] -> m Bool) -> Expr -> m Bool
checkPatterns check = cata $ \case
    LamS _ expr ->
        expr

    AppS exprs ->
        and <$> sequence exprs

    LetS _ expr body ->
        expr &&^ body

    LetRecS _ expr body ->
        expr &&^ body

    IfS cond true false ->
        cond &&^ true &&^ false

    OpS (AddS a b) -> a &&^ b
    OpS (SubS a b) -> a &&^ b
    OpS (MulS a b) -> a &&^ b
    OpS (EqS a b) -> a &&^ b
    OpS (LtS a b) -> a &&^ b
    OpS (GtS a b) -> a &&^ b
    OpS (NegS a) -> a
    OpS (NotS a) -> a

    StructS expr ->
        expr

    AnnS expr _ ->
        expr

    MatchS expr clss ->
        expr &&^ (checkClauses clss >>= check)

    LamMatchS clss ->
        checkClauses clss >>= check

    _ ->
        pure True

checkClauses :: (Monad m) => [MatchClause (m b)] -> m [MatchClause b]
checkClauses clss = do
    let (patterns, exprs) = unzip clss
    zip patterns <$> sequence exprs

allPatternsAreSimple :: Expr -> Bool
allPatternsAreSimple = 
    runIdentity . checkPatterns (pure . uncurry check . unzip) where
    check patterns exprs =
        and exprs &&
        and (isSimple <$> patterns)

allPatternsAreExhaustive :: Expr -> ConstructorEnv -> Bool
allPatternsAreExhaustive = runReader . checkPatterns (exhaustive . fmap fst)

-- ============================================================================
-- == Patterns Compiler
-- ============================================================================

type Equation = ([Pattern], Expr)

data ConHead = ConHead
    { conName  :: Name
    , conArity :: Int
    , conPats  :: [Pattern]
    , conExpr  :: Expr
    } deriving (Show, Eq)

data VarHead = VarHead
    { varName  :: Maybe Name
    , varPats  :: [Pattern]
    , varExpr  :: Expr
    } deriving (Show, Eq)

data LitHead = LitHead
    { litPrim  :: Prim
    , litPats  :: [Pattern]
    , litExpr  :: Expr
    } deriving (Show, Eq)

data EqGroup
    = ConEqs [ConHead]
    | VarEqs [VarHead]
    | LitEqs [LitHead]
    deriving (Show, Eq)

groups :: [Equation] -> [EqGroup]
groups eqs = grp:grps
  where
    (grp, grps) = foldr (uncurry arrange) (ConEqs [], []) eqs

    arrange (Fix (ConP name qs):ps) expr =
        let c = ConHead { conName  = name
                        , conArity = length qs
                        , conPats  = qs <> ps
                        , conExpr  = expr }
         in \case
            (ConEqs cs, gs) -> (ConEqs (c:cs), gs)
            (g, gs)         -> (ConEqs [c], g:gs)

    arrange (Fix (VarP name):ps) expr =
        let c = VarHead { varName = Just name
                        , varPats = ps
                        , varExpr = expr }
         in \case
            (VarEqs cs, gs) -> (VarEqs (c:cs), gs)
            (g, gs)         -> (VarEqs [c], g:gs)

    arrange (Fix AnyP:ps) expr =
        let c = VarHead { varName = Nothing
                        , varPats = ps
                        , varExpr = expr }
         in \case
            (VarEqs cs, gs) -> (VarEqs (c:cs), gs)
            (g, gs)         -> (VarEqs [c], g:gs)

    arrange (Fix (LitP prim):ps) expr =
        let c = LitHead { litPrim = prim
                        , litPats = ps
                        , litExpr = expr }
         in \case
            (LitEqs cs, gs) -> (LitEqs (c:cs), gs)
            (g, gs)         -> (LitEqs [c], g:gs)

    arrange [] _ = error "Implementation error"

data ConGroup = ConGroup
    { name      :: Name
    , arity     :: Int
    , equations :: [Equation]
    } deriving (Show)

conGroups :: [ConHead] -> [ConGroup]
conGroups qs =
    makeGroup <$> groupSortOn (\ConHead{..} -> (conName, conArity)) qs
  where
    makeGroup cs@(ConHead{ conName = name, conArity = arity }:_) = ConGroup
      { name      = name
      , arity     = arity
      , equations = (\ConHead{..} -> (conPats, conExpr)) <$> cs }

    makeGroup [] = error "Implementation error"

compilePatterns :: (MonadSupply Name m) => [Expr] -> [Equation] -> m Expr
compilePatterns = matchDefault errS

matchDefault :: (MonadSupply Name m) => Expr -> [Expr] -> [Equation] -> m Expr
matchDefault _ [] [([], expr)] = pure expr
matchDefault _ [] _ = error "Implementation error"
matchDefault d (u:us) qs = foldrM (flip run) d (groups qs)
  where
    run :: MonadSupply Name m => Expr -> EqGroup -> m Expr
    run def = \case
        ConEqs eqs -> do
            css <- traverse groupClause (conGroups eqs)
            pure $ case css <> [(anyP, def) | errS /= def] of
                [] -> def
                css' -> matchS u css'
          where
            groupClause :: MonadSupply Name m => ConGroup -> m (MatchClause Expr)
            groupClause ConGroup{..} = do
                vs <- replicateM arity supply
                expr <- matchDefault def ((varS <$> vs) <> us) equations
                pure (conP name (varP <$> vs), expr)

        VarEqs eqs ->
            matchDefault def us (fun <$> eqs) where
                fun VarHead{..} =
                    ( varPats
                    , case varName of
                          Nothing   -> varExpr
                          Just name -> apply (name `mapsTo` u) varExpr )

        LitEqs eqs ->
            foldrM fun def eqs where
                fun LitHead{..} false = do
                    true <- matchDefault def us [(litPats, litExpr)]
                    pure (ifS (eqS u (litS litPrim)) true false)

compileAll :: Expr -> Expr
compileAll = cata $ \case
    MatchS expr clss -> run expr clss
    LamMatchS clss   -> lamS "$" (run (varS "$") clss)
    expr             -> Fix expr
  where
    run :: Expr -> [MatchClause Expr] -> Expr
    run expr clss =
        first (:[]) <$> clss
            & compilePatterns [expr]
            & flip evalSupply (nameSupply ":")
            & fromJust
