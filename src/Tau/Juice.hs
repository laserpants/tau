{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StrictData                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
module Tau.Juice where

import Control.Arrow ((>>>), (***))
import Control.Monad.Except
import Control.Monad.Extra (anyM, (&&^))
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Data.Either.Extra (mapLeft)
import Data.Eq.Deriving
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.Functor.Const (Const(..))
import Data.Functor.Foldable
import Data.List (intersperse, find, delete, nub, elemIndex)
import Data.List.Extra (groupSortOn)
import Data.Map.Strict (Map, notMember, (!?))
import Data.Maybe (fromMaybe, fromJust)
import Data.Set.Monad (Set, union, intersection, member, (\\))
import Data.Text (Text, pack, unpack)
import Data.Tuple (swap)
import Data.Tuple.Extra (first, first3, both)
import Debug.Trace
import GHC.Show (showSpace)
import Text.Show.Deriving
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text

-- ============================================================================
-- =================================== Util ===================================
-- ============================================================================

type Name = Text

(#) = (&)

infixl 0 #

data (f :*: g) a = (:*:)
    { left  :: f a
    , right :: g a }
  deriving
    ( Eq
    , Show
    , Functor
    , Foldable
    , Traversable )

$(deriveShow1 ''(:*:))
$(deriveEq1   ''(:*:))

type Algebra f a = f a -> a

-- ============================================================================
-- =================================== Type ===================================
-- ============================================================================

-- | Type to represent types
data TypeF a
    = ConT Name            -- ^ Type constructor
    | VarT Name            -- ^ Type variable
    | ArrT a a             -- ^ Functions type
    | AppT a a             -- ^ Type application
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1   ''TypeF)

type Type = Fix TypeF

-- | Type class constraint
data Class = Class
    { className :: Name
    , classType :: Type
    } deriving (Show, Eq)

-- | Polymorphic type
data Scheme = Forall
    { schemeForall      :: [Name]
    , schemeConstraints :: [Class]
    , schemeType        :: Type
    } deriving (Show, Eq)

data KindF a
    = ArrowK a a           -- ^ Type arrow
    | StarK                -- ^ Concrete type
    | VarK Name            -- ^ Kind variable placeholder
    deriving (Show, Eq)

type Kind = Fix KindF

$(deriveShow1 ''KindF)
$(deriveEq1   ''KindF)

newtype Context a = Context (Map Name a)
    deriving (Show, Eq)

tInt, tInteger, tBool, tFloat, tString, tChar, tUnit, tVoid :: Type

tInt     = conT "Int"      -- ^ Int
tInteger = conT "Integer"  -- ^ Integer
tBool    = conT "Bool"     -- ^ Bool
tFloat   = conT "Float"    -- ^ Float
tString  = conT "String"   -- ^ String
tChar    = conT "Char"     -- ^ Char
tUnit    = conT "Unit"     -- ^ Unit
tVoid    = conT "Void"     -- ^ Void

-- ----------------------------------------------------------------------------
-- ---------------------------- Smart Constructors ----------------------------
-- ----------------------------------------------------------------------------

conT :: Name -> Type
conT = Fix . ConT

varT :: Name -> Type
varT = Fix . VarT

arrT :: Type -> Type -> Type
arrT a1 a2 = Fix (ArrT a1 a2)

appT :: Type -> Type -> Type
appT a1 a2 = Fix (AppT a1 a2)

arrowK :: Kind -> Kind -> Kind
arrowK a1 a2 = Fix (ArrowK a1 a2)

starK :: Kind
starK = Fix StarK

varK :: Name -> Kind
varK = Fix . VarK

-- ============================================================================
-- ============================ Type Substitution =============================
-- ============================================================================

newtype Substitution a = Substitution { getSubstitution :: Map Name a }
    deriving (Show, Eq, Functor)

compose :: (Substitutable a a) => Substitution a -> Substitution a -> Substitution a
compose sub@(Substitution map1) (Substitution map2) =
    Substitution (Map.union (Map.map (apply sub) map2) map1)

substitute :: Name -> a -> Substitution a
substitute name = Substitution . Map.singleton name

class Substitutable t a where
    apply :: Substitution t -> a -> a

instance (Substitutable a a) => Semigroup (Substitution a) where
    (<>) = compose

instance (Substitutable a a) => Monoid (Substitution a) where
    mempty = Substitution mempty

instance (Substitutable t a) => Substitutable t [a] where
    apply = fmap . apply

instance Substitutable Type Type where
    apply sub ty@(Fix (VarT var)) = Map.findWithDefault ty var (getSubstitution sub)
    apply sub (Fix (ArrT t1 t2))  = arrT (apply sub t1) (apply sub t2)
    apply sub (Fix (AppT t1 t2))  = appT (apply sub t1) (apply sub t2)
    apply _ ty                    = ty

instance Substitutable Type Class where
    apply sub (Class name ty) = Class name (apply sub ty)

instance Substitutable Type Scheme where
    apply (Substitution map) (Forall vars clcs ty) =
        Forall vars (apply sub clcs) (apply sub ty)
      where
        sub = Substitution (foldr Map.delete map vars)

instance Substitutable Kind Kind where
    apply sub (Fix (VarK name))    = Map.findWithDefault (varK name) name (getSubstitution sub)
    apply sub (Fix (ArrowK k1 k2)) = arrowK (apply sub k1) (apply sub k2)
    apply _ (Fix StarK)            = starK

-- | Class of types that contain free type variables
class Free t where
    free :: t -> Set Name

instance (Free t) => Free [t] where
    free = foldr (union . free) mempty

instance Free Type where
    free (Fix (VarT var))   = Set.singleton var
    free (Fix (ArrT t1 t2)) = free t1 `union` free t2
    free (Fix (AppT t1 t2)) = free t1 `union` free t2
    free _                  = mempty

instance Free Scheme where
    free (Forall vars _ ty) = free ty \\ Set.fromList vars

instance (Free a) => Free (Context a) where
    free (Context env) = free (Map.elems env)

instance Free Kind where
    free (Fix (ArrowK k l)) = free k `union` free l
    free (Fix (VarK name))  = Set.singleton name
    free _                  = mempty

occursIn :: (Free t) => Name -> t -> Bool
occursIn var ty = var `member` free ty

-- ============================================================================
-- =================================== Ast ====================================
-- ============================================================================

-- | Language primitives
data Prim
    = Unit                   -- ^ Unit value
    | Bool Bool              -- ^ Boolean
    | Int Int                -- ^ Machine-level integers (32 or 64 bit)
    | Integer Integer        -- ^ Arbitrary precision integer
    | Float Double           -- ^ Floating point number
    | Char Char              -- ^ Char
    | String Text            -- ^ String
    deriving (Show, Eq)

data PatternF a
    = VarP Name              -- ^ Variable pattern
    | ConP Name [a]          -- ^ Constuctor pattern
    | LitP Prim              -- ^ Literal pattern
    | AnyP                   -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

$(deriveShow1 ''PatternF)
$(deriveEq1   ''PatternF)

type Pattern = Fix PatternF

-- | Source language expression tree
data ExprF a
    = VarS Name
    | LamS Name a
    | AppS [a]
    | LitS Prim
    | LetS Name a a
    | RecS Name a a
    | IfS a ~a ~a
    | MatchS a [(Pattern, a)]
    | OpS (OpF a)
    | AnnS a Type
    | ErrS
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Expr = Fix ExprF

-- | Operators
data OpF a
    = AddS a a
    | SubS a a
    | MulS a a
    | DivS a a
    | EqS a a
    | LtS a a
    | GtS a a
    | NegS a
    | NotS a
    | OrS ~a ~a
    | AndS ~a ~a
    deriving (Show, Eq, Functor, Foldable, Traversable)

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)

$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)

-- ============================================================================
-- ================================= Patterns =================================
-- ============================================================================

patternVars :: Pattern -> [Name]
patternVars = cata alg where
    alg :: Algebra PatternF [Name]
    alg (VarP v)    = [v]
    alg (ConP _ ps) = concat ps
    alg _           = []

-- | A simple pattern is a variable, a wildcard, or a constructor where all the
-- subpatterns are simple.
isSimple :: Pattern -> Bool
isSimple = fun . unfix where
    fun AnyP        = True
    fun VarP{}      = True
    fun (ConP _ ps) = all isSimple ps
    fun _           = False

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

type Lookup = Map Name (Set Name)

lookupFromList :: [(Name, [Name])] -> Lookup
lookupFromList = Map.fromList . fmap (fmap Set.fromList)

type PatternCheckTStack m a = ReaderT Lookup m a

newtype PatternCheckT m a = PatternCheckT (PatternCheckTStack m a) deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader Lookup )

runPatternCheckT :: PatternCheckT m a -> Lookup -> m a
runPatternCheckT (PatternCheckT a) = runReaderT a

type PatternCheck = PatternCheckT Identity

runPatternCheck :: PatternCheck a -> Lookup -> a
runPatternCheck a = runIdentity . runPatternCheckT a

headCons :: (Monad m) => [[Pattern]] -> m [(Name, Int)]
headCons = fmap concat . traverse fun where
    fun [] = error "Fatal error in pattern anomalies check"
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

useful :: (MonadReader Lookup m) => [[Pattern]] -> [Pattern] -> m Bool
useful [] qs = pure True        -- zero rows (0x0 matrix)
useful px@(ps:_) qs =
    case (qs, length ps) of
        (_, 0) -> pure False    -- one or more rows but no columns

        ([], _) ->
            error "Fatal error in pattern anomalies check"

        (Fix (ConP name rs):_, n) ->
            let special = specialized name (length rs)
             in useful (special px) (head (special [qs]))

        (_:qs1, n) -> do
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
        lookup <- ask
        let map = lookup `Map.union` lookupFromList builtIn
        pure (Map.findWithDefault mempty name map == Set.fromList names)

    builtIn =
        [ ("$True",     ["$True", "$False"])
        , ("$False",    ["$True", "$False"])
        , ("$()",       ["$()"])
        , ("$Int",      [])
        , ("$Integer",  [])
        , ("$Float",    [])
        , ("$Char",     [])
        , ("$String",   [])
        ]

exhaustive :: (Monad m) => [Pattern] -> PatternCheckT m Bool
exhaustive ps = not <$> useful ((:[]) <$> ps) [anyP]

checkPatterns :: (Monad m) => ([(Pattern, Bool)] -> m Bool) -> Expr -> m Bool
checkPatterns pred = cata $ \case
    LamS _ expr ->
        expr

    AppS exprs ->
        and <$> sequence exprs

    LetS _ expr body ->
        expr &&^ body

    RecS _ expr body ->
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

    AnnS expr _ ->
        expr

    MatchS expr clss -> do
        let (patterns, exprs) = unzip clss
        clss' <- zip patterns <$> sequence exprs
        expr &&^ pred clss'

    _ ->
        pure True

allPatternsAreSimple :: (Monad m) => Expr -> m Bool
allPatternsAreSimple = checkPatterns (pure . uncurry pred . unzip) where
    pred patterns exprs =
        and exprs &&
        and (isSimple <$> patterns)

allPatternsAreExhaustive :: (Monad m) => Expr -> Lookup -> m Bool
allPatternsAreExhaustive =
    runPatternCheckT . checkPatterns (exhaustive . fmap fst)

-- ============================================================================
-- ============================ Patterns Compiler =============================
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
groups qs = cs:gs
  where
    (cs, gs) = foldr (uncurry arrange) (ConEqs [], []) qs

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
      , equations = (\ConHead{..} -> (conPats, conExpr)) <$> cs }

type PatternMatchCompilerTStack m a = SupplyT Name m a

newtype PatternMatchCompilerT m a = PatternMatchCompilerT (PatternMatchCompilerTStack m a)
  deriving (Functor, Applicative, Monad, MonadSupply Name)

runPatternMatchCompilerT :: (Monad m) => PatternMatchCompilerT m a -> m a
runPatternMatchCompilerT (PatternMatchCompilerT a) =
    evalSupplyT a (pfxed <$> [1..])
  where
    pfxed count = ":" <> pack (show count)

type PatternMatchCompiler = PatternMatchCompilerT Identity

runPatternMatchCompiler :: PatternMatchCompiler a -> a
runPatternMatchCompiler = runIdentity . runPatternMatchCompilerT

compilePatterns :: (MonadSupply Name m) => [Expr] -> [Equation] -> m Expr
compilePatterns = matchDefault errS

matchDefault :: (MonadSupply Name m) => Expr -> [Expr] -> [Equation] -> m Expr
matchDefault _ [] [([], expr)] = pure expr
matchDefault def (u:us) qs = foldrM (flip run) def (groups qs) where
    run :: MonadSupply Name m => Expr -> EqGroup -> m Expr
    run def = \case
        ConEqs eqs -> do
            css <- traverse groupClause (conGroups eqs)
            pure $ case css <> [(anyP, def) | errS /= def] of
                [] -> def
                css' -> matchS u css'
          where
            groupClause :: MonadSupply Name m => ConGroup -> m (Pattern, Expr)
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
                          Just name -> substituteExpr name u varExpr )

        LitEqs eqs ->
            foldrM fun def eqs where
                fun LitHead{..} false = do
                    true <- matchDefault def us [(litPats, litExpr)]
                    pure (ifS (eqS u (litS litPrim)) true false)

compileAll :: Expr -> Expr
compileAll = cata $ \case
    MatchS expr clss ->
        runPatternMatchCompiler (compilePatterns [expr] (first (:[]) <$> clss))

    expr ->
        Fix expr

-- ----------------------------------------------------------------------------
-- ---------------------------- Smart Constructors ----------------------------
-- ----------------------------------------------------------------------------

-- | VarS constructor
varS :: Name -> Expr
varS = Fix . VarS

-- | LamS constructor
lamS :: Name -> Expr -> Expr
lamS a = Fix . LamS a

-- | AppS constructor
appS :: [Expr] -> Expr
appS = Fix . AppS

-- | LitS constructor
litS :: Prim -> Expr
litS = Fix . LitS

-- | LetS constructor
letS :: Name -> Expr -> Expr -> Expr
letS a1 a2 = Fix . LetS a1 a2

-- | RecS constructor
recS :: Name -> Expr -> Expr -> Expr
recS a1 a2 = Fix . RecS a1 a2

-- | IfS constructor
ifS :: Expr -> Expr -> Expr -> Expr
ifS a1 a2 a3 = Fix (IfS a1 a2 a3)

-- | MatchS constructor
matchS :: Expr -> [(Pattern, Expr)] -> Expr
matchS a = Fix . MatchS a

-- | OpS constructor
opS :: OpF Expr -> Expr
opS = Fix . OpS

annS :: Expr -> Type -> Expr
annS a = Fix . AnnS a

errS :: Expr
errS = Fix ErrS

-- | AddS constructor
addS :: Expr -> Expr -> Expr
addS a1 a2 = opS (AddS a1 a2)

-- | SubS constructor
subS :: Expr -> Expr -> Expr
subS a1 a2 = opS (SubS a1 a2)

-- | MulS constructor
mulS :: Expr -> Expr -> Expr
mulS a1 a2 = opS (MulS a1 a2)

-- | DivS constructor
divS :: Expr -> Expr -> Expr
divS a1 a2 = opS (DivS a1 a2)

-- | EqS constructor
eqS :: Expr -> Expr -> Expr
eqS a1 a2 = opS (EqS a1 a2)

-- | LtS constructor
ltS :: Expr -> Expr -> Expr
ltS a1 a2 = opS (LtS a1 a2)

-- | GtS constructor
gtS :: Expr -> Expr -> Expr
gtS a1 a2 = opS (GtS a1 a2)

-- | NegS constructor
negS :: Expr -> Expr
negS = opS . NegS

-- | NotS constructor
notS :: Expr -> Expr
notS = opS . NotS

orS :: Expr -> Expr -> Expr
orS a1 a2 = opS (OrS a1 a2)

andS :: Expr -> Expr -> Expr
andS a1 a2 = opS (AndS a1 a2)

litUnit :: Expr
litUnit = litS Unit

litBool :: Bool -> Expr
litBool = litS . Bool

litInt :: Int -> Expr
litInt = litS . Int

litInteger :: Integer -> Expr
litInteger = litS . Integer

litFloat :: Double -> Expr
litFloat = litS . Float

litChar :: Char -> Expr
litChar = litS . Char

litString :: Text -> Expr
litString = litS . String

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

-- ============================================================================
-- ============================== Kind Inference ==============================
-- ============================================================================

type KindAssumption = (Name, Kind)
type KindConstraint = (Kind, Kind)

instance Substitutable KindConstraint KindConstraint where
    apply sub = apply (fst <$> sub) *** apply (snd <$> sub)

runInferK :: (Monad m) => SupplyT Kind m a -> m a
runInferK = flip evalSupplyT (varK . pack . show <$> [1..])

inferK
  :: (MonadSupply Kind m)
  => Type
  -> m (Kind, [KindAssumption], [KindConstraint])
inferK = cata alg where
    alg
      :: (MonadSupply Kind m)
      => Algebra TypeF (m (Kind, [KindAssumption], [KindConstraint]))
    alg = \case
        ArrT t1 t2 -> do
            (k1, as1, cs1) <- t1
            (k2, as2, cs2) <- t2
            pure ( starK
                  , as1 <> as2
                  , cs1 <> cs2 <> [(k1, starK), (k2, starK)] )

        AppT t1 t2 -> do
            (k1, as1, cs1) <- t1
            (k2, as2, cs2) <- t2
            kvar <- supply
            pure ( kvar
                 , as1 <> as2
                 , cs1 <> cs2 <> [(k1, arrowK k2 kvar)] )

        ConT con | isPrim con ->
            pure ( starK, [], [] )

        ConT con -> assumeVar con
        VarT var -> assumeVar var

    assumeVar name = do
        kvar <- supply
        pure ( kvar, [(name, kvar)], [] )

inferKind :: (MonadSupply Kind m) => Context Kind -> Type -> m Kind
inferKind (Context env) ty = do
    (kind, as, cs) <- inferK ty
    sub <- solveKinds (cs <> envConstraints as)
    pure (apply sub kind)
  where
    envConstraints :: [KindAssumption] -> [KindConstraint]
    envConstraints as = do
        (x, k) <- as
        (y, l) <- Map.toList env
        guard (x == y)
        pure (k, l)

isPrim :: Name -> Bool
isPrim "Int"     = True
isPrim "Integer" = True
isPrim "Bool"    = True
isPrim "Float"   = True
isPrim "String"  = True
isPrim "Char"    = True
isPrim "Unit"    = True
isPrim "Void"    = True
isPrim _         = False

--instance Unifiable Kind where
--    toVar = varK
--    unify (Fix (ArrowK k1 k2)) (Fix (ArrowK l1 l2)) = 
--        unifyPairX (k1, k2) (l1, l2)
--    unify (Fix (VarK k1)) k2 = bindX k1 k2
--    unify k1 (Fix (VarK k2)) = bindX k2 k1
--    unify k1 k2 = unifyDefaultX k1 k2

bindKinds :: (Monad m) => Name -> Kind -> m (Substitution Kind)
bindKinds var kind
    | varK var == kind    = pure mempty
    | var `occursIn` kind = error "Infinite type"
    | otherwise           = pure (substitute var kind)

unifyKinds :: (Monad m) => Kind -> Kind -> m (Substitution Kind)
unifyKinds (Fix (ArrowK k1 k2)) (Fix (ArrowK l1 l2)) = do
    sub1 <- unifyKinds k1 l1
    sub2 <- unifyKinds (apply sub1 k2) (apply sub1 l2)
    pure (sub2 <> sub1)
unifyKinds (Fix (VarK k1)) k2 = bindKinds k1 k2
unifyKinds k1 (Fix (VarK k2)) = bindKinds k2 k1
unifyKinds k1 k2
    | k1 == k2  = pure mempty
    | otherwise = error "Cannot unify"

solveKinds :: (Monad m) => [KindConstraint] -> m (Substitution Kind)
solveKinds [] = pure mempty
solveKinds ((k1, k2):cs) = do
    sub1 <- unifyKinds k1 k2
    sub2 <- solveKinds (both (apply sub1) <$> cs)
    pure (sub2 <> sub1)

-- ============================================================================
-- ============================== Type Inference ==============================
-- ============================================================================

data TypeError
    = CannotSolve
    | CannotUnify
    | InfiniteType
--    | UnificationError UnificationError
    | UnboundVariable Name
    | EmptyMatchStatement
    | ImplementationError
    deriving (Show, Eq)

instance (Monad m) => MonadFail (InferT m) where
    fail = const (throwError ImplementationError)

instance MonadTrans InferT where
    lift = InferT . lift . lift . lift

type InferTStack m a = ReaderT Monoset (ExceptT TypeError (SupplyT Type m)) a

newtype InferT m a = InferT (InferTStack m a) deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader Monoset
    , MonadSupply Type
    , MonadError TypeError )

freshVars :: [Type]
freshVars = varT . pfxed <$> [1..] where
    pfxed count = "a" <> pack (show count)

runInferT :: (Monad m) => InferT m a -> m (Either TypeError a)
runInferT (InferT a) =
    freshVars
        # Monoset mempty
        & runReaderT a
        & runExceptT
        & evalSupplyT

type Infer a = InferT Identity a

runInfer :: Infer a -> Either TypeError a
runInfer = runIdentity . runInferT

-- | Monomorphic set
newtype Monoset = Monoset (Set Name)
    deriving (Show, Eq)

insertIntoMonoset :: Name -> Monoset -> Monoset
insertIntoMonoset var (Monoset set) = Monoset (Set.insert var set)

insertManyIntoMonoset :: [Name] -> Monoset -> Monoset
insertManyIntoMonoset = flip (foldr insertIntoMonoset)

instance Free Monoset where
    free (Monoset set) = set

instance Substitutable Type Monoset where
    apply sub (Monoset set) = Monoset (free . apply sub . varT =<< set)

type AnnotatedExprF a = Const a :*: ExprF

-- | Type-annotated syntax tree
newtype AnnotatedExpr a = AnnotatedExpr
    { runAnnotatedExpr :: Fix (AnnotatedExprF a) }
    deriving (Eq, Show)

instance Substitutable Type (AnnotatedExpr Type) where
    apply sub = runAnnotatedExpr >>> cata alg >>> AnnotatedExpr where
        alg (Const ty :*: expr) = Fix (Const (apply sub ty) :*: expr)

getExpr :: AnnotatedExpr a -> Expr
getExpr = cata (Fix . right) . runAnnotatedExpr

getAnnotation :: AnnotatedExpr a -> a
getAnnotation =
    getConst
      . left
      . unfix
      . runAnnotatedExpr

infer
  :: (Monad m)
  => Expr
  -> InferT m (AnnotatedExpr Type, [Assumption], [Constraint])
infer = cata alg where
    alg :: (Monad m)
        => Algebra ExprF (InferT m (AnnotatedExpr Type, [Assumption], [Constraint]))
    alg = fmap expand >>> \case
        VarS name -> do
            beta <- supply
            pure ( annotated beta (VarS name)
                 , [Assumption (name, beta)]
                 , [] )

        LamS name expr -> do
            beta@(Fix (VarT var)) <- supply
            (_expr, t1, a1, c1) <- local (insertIntoMonoset var) expr
            pure ( annotated (arrT beta t1) (LamS name _expr)
                 , removeAssumption name a1
                 , c1 <> [Equality t beta | (y, t) <- runAssumption <$> a1, name == y] )

        AppS exprs -> do
            (_expr, _, as, cs) <- foldl1 inferApp exprs
            pure ( AnnotatedExpr _expr, as, cs )

        LitS prim -> do
            t <- inferPrim prim
            pure ( annotated t (LitS prim), [], [] )

        LetS var expr body ->
            inferLet var expr body False

        RecS var expr body ->
            inferLet var expr body True

        IfS cond true false -> do
            (_cond, t1, a1, c1) <- cond
            (_true, t2, a2, c2) <- true
            (_false, t3, a3, c3) <- false
            pure ( annotated t2 (IfS _cond _true _false)
                 , a1 <> a2 <> a3
                 , c1 <> c2 <> c3 <> [Equality t1 tBool, Equality t2 t3] )

        MatchS _ [] ->
            throwError EmptyMatchStatement

        MatchS expr clss -> do
            beta <- supply
            (_expr, t1, a1, c1) <- expr
            (_clss, as, cs) <- foldrM (inferClause beta t1) ([], [], []) clss
            pure ( annotated beta (MatchS _expr _clss)
                 , a1 <> as
                 , c1 <> cs )

        OpS op ->
            inferOp op

        AnnS expr ty ->
            undefined  -- TODO

inferLet
  :: (MonadReader Monoset m)
  => Name
  -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> Bool
  -> m (AnnotatedExpr Type, [Assumption], [Constraint])
inferLet var expr body rec = do
    (_e1, t1, a1, c1) <- expr
    (_e2, t2, a2, c2) <- body
    set <- ask
    pure ( annotated t2 ((if rec then RecS else LetS) var _e1 _e2)
         , (if rec then removeAssumption var a1 else a1) <> removeAssumption var a2
         , c1 <> c2 <> [Implicit t t1 set | (y, t) <- runAssumption <$> a1 <> a2, var == y] )

type Clause = (Pattern, Fix (AnnotatedExprF Type))

inferClause
  :: (Monad m)
  => Type
  -> Type
  -> (Pattern, InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint]))
  -> ([Clause], [Assumption], [Constraint])
  -> InferT m ([Clause], [Assumption], [Constraint])
inferClause beta t (pat, expr) (ps, as, cs) = do
    (_expr, t1, a1, c1) <- local (insertManyIntoMonoset vars) expr
    (t2, a2, c2) <- inferPattern pat
    pure ( (pat, _expr):ps
         , as <> removeManyAssumptions vars a1
              <> removeManyAssumptions vars a2
         , cs <> c1 <> c2
              <> [Equality beta t1, Equality t t2]
              <> constraints a1 a2 )
  where
    vars = patternVars pat
    constraints a1 a2 = do
        (y1, t1) <- runAssumption <$> a1
        (y2, t2) <- runAssumption <$> a2
        var <- vars
        guard (var == y1 && var == y2)
        pure (Equality t1 t2)

inferPattern :: (Monad m) => Pattern -> InferT m (Type, [Assumption], [Constraint])
inferPattern = cata $ \case
    VarP var -> do
        beta <- supply
        pure (beta, [Assumption (var, beta)], [])

    ConP name ps -> do
        beta <- supply
        (ts, ass, css) <- (fmap unzip3 . sequence) ps
        pure ( beta
             , concat ass <> [Assumption (name, foldr arrT beta ts)]
             , concat css )

    LitP prim -> do
        t <- inferPrim prim
        pure (t, [], [])

    AnyP -> do
        beta <- supply
        pure (beta, [], [])

inferApp
  :: (Monad m)
  => InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
  -> InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
inferApp fun arg = do
    (_e1, t1, a1, c1) <- fun
    (_e2, t2, a2, c2) <- arg
    beta <- supply
    pure ( Fix (Const beta :*: AppS [_e1, _e2])
         , beta
         , a1 <> a2
         , c1 <> c2 <> [Equality t1 (arrT t2 beta)] )

op1
  :: (MonadSupply Type m) =>
     (Fix (AnnotatedExprF Type) -> OpF (Fix (AnnotatedExprF Type)))
     -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
     -> Scheme
     -> m (AnnotatedExpr Type, [Assumption], [Constraint])
op1 con e1 sig = do
    (_e1, t1, a1, c1) <- e1
    beta <- supply
    pure ( annotated beta (OpS (con _e1))
         , a1
         , c1 <> [Explicit (arrT t1 beta) sig] )

op2
  :: (MonadSupply Type m) =>
     (Fix (AnnotatedExprF Type) -> Fix (AnnotatedExprF Type) -> OpF (Fix (AnnotatedExprF Type)))
     -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
     -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
     -> Scheme
     -> m (AnnotatedExpr Type, [Assumption], [Constraint])
op2 con e1 e2 sig = do
    (_e1, t1, a1, c1) <- e1
    (_e2, t2, a2, c2) <- e2
    beta <- supply
    pure ( annotated beta (OpS (con _e1 _e2))
         , a1 <> a2
         , c1 <> c2 <> [Explicit (arrT t1 (arrT t2 beta)) sig] )

inferOp
  :: (Monad m)
  => OpF (InferT m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint]))
  -> InferT m (AnnotatedExpr Type, [Assumption], [Constraint])
inferOp = \case
    AddS e1 e2 -> op2 AddS e1 e2 numericOp2
    SubS e1 e2 -> op2 SubS e1 e2 numericOp2
    MulS e1 e2 -> op2 MulS e1 e2 numericOp2
    DivS e1 e2 -> op2 DivS e1 e2 numericOp2
    LtS e1 e2 -> op2 LtS e1 e2 comparisonOp
    GtS e1 e2 -> op2 GtS e1 e2 comparisonOp
    EqS e1 e2 -> op2 EqS e1 e2 equalityOp
    NegS e -> op1 NegS e numericOp1
    NotS e -> op1 NotS e numericOp1
    OrS e1 e2 -> op2 OrS e1 e2 logicalOp
    AndS e1 e2 -> op2 AndS e1 e2 logicalOp

numericOp1 :: Scheme
numericOp1 =
    Forall ["a"]
    [Class "Num" (varT "a")]
    (arrT (varT "a") (varT "a"))

numericOp2 :: Scheme
numericOp2 =
    Forall ["a"]
    [Class "Num" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") (varT "a")))

equalityOp :: Scheme
equalityOp =
    Forall ["a"]
    [Class "Eq" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") tBool))

comparisonOp :: Scheme
comparisonOp =
    Forall ["a"]
    [Class "Ord" (varT "a")]
    (arrT (varT "a") (arrT (varT "a") tBool))

logicalOp :: Scheme
logicalOp =
    Forall []
    []
    (arrT tBool (arrT tBool tBool))

inferPrim :: (Monad m) => Prim -> InferT m Type
inferPrim = pure . \case
    Unit      -> tUnit
    Bool{}    -> tBool
    Int{}     -> tInt
    Integer{} -> tInteger
    Float{}   -> tFloat
    Char{}    -> tChar
    String{}  -> tString

solveExprType
  :: (Monad m)
  => Context Scheme
  -> Expr
  -> InferT m (AnnotatedExpr Type, Substitution Type, [Class])
solveExprType (Context env) expr = do
    (ty, as, cs) <- infer expr
    case unboundVars env as of
        (var:_) ->
            throwError (UnboundVariable var)

        [] -> do
            (sub, clcs) <- runStateT (solve (cs <> envConstraints as)) []
            pure (ty, sub, clcs)
  where
    envConstraints :: [Assumption] -> [Constraint]
    envConstraints as = do
        (x, s) <- runAssumption <$> as
        (y, t) <- Map.toList env
        guard (x == y)
        pure (Explicit s t)

inferType :: (Monad m) => Context Scheme -> Expr -> InferT m (AnnotatedExpr Scheme)
inferType context expr = do
    (ty, sub, clcs) <- solveExprType context expr
--    traceShowM (apply sub (getAnnotation ty))
--    traceShowM (apply sub clcs)
    annotate sub ty
  where
    annotate
      :: (Monad m)
      => Substitution Type
      -> AnnotatedExpr Type
      -> InferT m (AnnotatedExpr Scheme)
    annotate sub = cata alg . runAnnotatedExpr where
        alg :: Monad m => Algebra (AnnotatedExprF Type) (InferT m (AnnotatedExpr Scheme))
        alg (Const ty :*: expr) = do
            zz <- fmap runAnnotatedExpr <$> sequence expr
            ----pure $ annotated (generalize mempty [] (apply sub ty)) zz
            pure $ annotated (generalize mempty (apply sub ty)) zz

--    annotate
--      :: (Monad m)
--      => Map Name Signature
--      -> AnnotatedExpr Type
--      -> InferT m (AnnotatedExpr Scheme)
--    annotate map = cata alg . runAnnotatedExpr
--      where
--        alg
--          :: (Monad m)
--          => Algebra (AnnotatedExprF Type) (InferT m (AnnotatedExpr Scheme))
--        alg (Const ty :*: expr) =
--            forall (applySigMap map [] ty) . fmap runAnnotatedExpr <$> sequence expr
--        forall (clcs, ty) =
--            let
--                cod = enumFrom 1 >>= fmap (VarT . pack) . flip replicateM ['a'..'z']
--                dom = nub $ Set.toList $ free ty
--                sub = Substitution $ Map.fromList (dom `zip` cod)
--                ty' = apply sub ty
--                clcs' = filter (\(Class _ ty) -> and [var `elem` free ty' | var <- Set.toList (free ty)]) clcs
--                -- TODO --
--             in annotated $ generalize mempty (apply sub clcs') ty'

unboundVars :: Map Name a -> [Assumption] -> [Name]
unboundVars env as = filter (`notMember` env) (fst . runAssumption <$> as)

annotated :: t -> ExprF (Fix (AnnotatedExprF t)) -> AnnotatedExpr t
annotated t a = AnnotatedExpr $ Fix $ Const t :*: a

expand
  :: (Monad m)
  => m (AnnotatedExpr Type, [Assumption], [Constraint])
  -> m (Fix (AnnotatedExprF Type), Type, [Assumption], [Constraint])
expand triple = do
    (e, as, cs) <- first3 runAnnotatedExpr <$> triple
    let Const t :*: _ = unfix e
    pure (e, t, as, cs)

-- ============================================================================
-- ============================ Constraints Solver ============================
-- ============================================================================

newtype Assumption = Assumption { runAssumption :: (Name, Type) }
    deriving (Show, Eq)

removeAssumption :: Name -> [Assumption] -> [Assumption]
removeAssumption var = filter fun where fun (Assumption a) = fst a /= var

removeManyAssumptions :: [Name] -> [Assumption] -> [Assumption]
removeManyAssumptions = flip (foldr removeAssumption)

data Constraint
    = Equality Type Type
    | Implicit Type Type Monoset
    | Explicit Type Scheme
    deriving (Show, Eq)

instance Substitutable Type Constraint where
    apply sub (Equality t1 t2)      = Equality (apply sub t1) (apply sub t2)
    apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
    apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)

class Active a where
    active :: a -> Set Name

instance Active Constraint where
    active (Equality t1 t2)      = free t1 `union` free t2
    active (Implicit t1 t2 mono) = free t1 `union` (free mono `intersection` free t2)
    active (Explicit ty scheme)  = free ty `union` free scheme

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active

isSolvable :: [Constraint] -> Constraint -> Bool
isSolvable cs (Implicit _ t2 (Monoset vars)) =
    Set.null (free t2 \\ vars `intersection` active cs)
isSolvable _ _ = True

choice :: [Constraint] -> Maybe ([Constraint], Constraint)
choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]

solve
  :: (MonadError TypeError m, MonadSupply Type m)
  => [Constraint]
  -> StateT [Class] m (Substitution Type)
solve [] = pure mempty
solve xs =
    maybe (throwError CannotSolve) pure (choice xs) >>= uncurry run
  where
    run cs = \case
        Equality t1 t2 -> do
            sub1 <- unify t1 t2
            modify (apply sub1)
            sub2 <- solve (apply sub1 cs)
            modify (apply sub2)
            pure (sub2 <> sub1)

        Implicit t1 t2 (Monoset vars) ->
            solve (Explicit t1 (generalize vars t2):cs)

        Explicit t1 scheme -> do
            t2 <- instantiate scheme
            solve (Equality t1 t2:cs)

generalize :: Set Name -> Type -> Scheme
generalize vars ty = Forall (Set.toList (free ty \\ vars)) [] ty

instantiate :: (MonadSupply Type m, MonadState [Class] m) => Scheme -> m Type
instantiate (Forall vars clcs ty) = do
    sub <- Substitution . map <$> traverse (const supply) vars
    modify (nub . apply sub . (<> clcs))
    pure (apply sub ty)
  where
    map = Map.fromList . zip vars

-- ============================================================================
-- ============================= Type Unification =============================
-- ============================================================================

-- data UnificationError 
--     = CannotUnify 
--     | InfiniteType 
--     deriving (Show, Eq)
-- 
-- class Unifiable t where
--     unify :: (MonadError UnificationError m) => t -> t -> m (Substitution t)
--     toVar :: Name -> t
--     err1 :: UnificationError
--     err2 :: UnificationError
-- 
-- instance Unifiable Type where
--     toVar = varT
--     unify (Fix (ArrT t1 t2)) (Fix (ArrT u1 u2)) = unifyPairX (t1, t2) (u1, u2)
--     unify (Fix (AppT t1 t2)) (Fix (AppT u1 u2)) = unifyPairX (t1, t2) (u1, u2)
--     unify (Fix (VarT a)) t = bindX a t
--     unify t (Fix (VarT a)) = bindX a t
--     unify t u = unifyDefaultX t u
-- 
-- --bindX 
-- --  :: (MonadError UnificationError m, Eq a, Unifiable a, Free a, Substitutable a a) 
-- --  => Name 
-- --  -> a 
-- --  -> m (Substitution a)
-- bindX var ty
--     | toVar var == ty   = pure mempty
--     | var `occursIn` ty = throwError InfiniteType
--     | otherwise         = pure (substitute var ty)
-- 
-- --unifyPairX 
-- --    :: (MonadError UnificationError m, Unifiable a, Substitutable a a) 
-- --    => (a, a)
-- --    -> (a, a)
-- --    -> m (Substitution a)
-- unifyPairX (t1, t2) (u1, u2) = do
--     sub1 <- unify t1 u1
--     sub2 <- unify (apply sub1 t2) (apply sub1 u2)
--     pure (sub2 <> sub1)
-- 
-- --unifyDefaultX :: (MonadError UnificationError m, Eq a, Substitutable a a) => a -> a -> m (Substitution a)
-- unifyDefaultX t u
--     | t == u    = pure mempty
--     | otherwise = throwError CannotUnify
-- 
-- -- <<

bind :: (MonadError TypeError m) => Name -> Type -> m (Substitution Type)
bind var ty
    | varT var == ty    = pure mempty
    | var `occursIn` ty = throwError InfiniteType
    | otherwise         = pure (substitute var ty)

unifyPair :: (MonadError TypeError m) => (Type, Type) -> (Type, Type) -> m (Substitution Type)
unifyPair (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

unify :: (MonadError TypeError m) => Type -> Type -> m (Substitution Type)
unify (Fix (ArrT t1 t2)) (Fix (ArrT u1 u2)) = unifyPair (t1, t2) (u1, u2)
unify (Fix (AppT t1 t2)) (Fix (AppT u1 u2)) = unifyPair (t1, t2) (u1, u2)
unify (Fix (VarT a)) t = bind a t
unify t (Fix (VarT a)) = bind a t
unify t u
    | t == u    = pure mempty
    | otherwise = throwError CannotUnify

-- ============================================================================
-- =================================== Value ==================================
-- ============================================================================

-- | The environment is a mapping from variables to values.
type Env m = Map Name (Value m)

-- | An expression evaluates to a primitive value, a fully applied data
-- constructor, or a function closure.
data Value m
    = Value Prim                           -- ^ Literal value
    | Data Name [Value m]                  -- ^ Applied data constructor
    | Closure Name (m (Value m)) ~(Env m)  -- ^ Function closure

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
        showString "<<function>>"

dataCon :: (MonadReader (Env m) m) => Name -> Int -> Value m
dataCon name 0 = Data name []
dataCon name n = Closure (varName 1) val mempty
  where
    val = tail vars
        # init
        & foldr (\name -> asks . Closure name)

    init = do
        env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)

    vars = varName <$> [1..n]
    varName n = "%" <> pack (show n)

-- ============================================================================
-- =============================== Substitution ===============================
-- ============================================================================

substituteExpr :: Name -> Expr -> Expr -> Expr
substituteExpr name val = para $ \case
    VarS var
        | name == var -> val
        | otherwise   -> varS var

    LamS var (expr, body)
        | name == var -> lamS var expr
        | otherwise   -> lamS var body

    AppS exprs ->
        appS (snd <$> exprs)

    LitS prim ->
        litS prim

    LetS var body expr ->
        substituteLet name var body expr False

    RecS var body expr ->
        substituteLet name var body expr True

    IfS cond true false ->
        ifS (snd cond) (snd true) (snd false)

    MatchS expr clss ->
        matchS (snd expr) (fun <$> clss) where
            fun (p, e) = (p, if name `elem` patternVars p then fst e else snd e)

    OpS op ->
        opS (snd <$> op)

    AnnS expr ty ->
        annS (snd expr) ty

  where
    substituteLet :: Name -> Name -> (Expr, Expr) -> (Expr, Expr) -> Bool -> Expr
    substituteLet name var body expr rec =
        let get = if name == var then fst else snd
         in (if rec then recS else letS) var (get body) (get expr)

-- ============================================================================
-- =================================== Eval ===================================
-- ============================================================================

data EvalError
    = RuntimeError
    | UnboundIdentifier Name
    | NonSimplePattern
    | TypeMismatch
    deriving (Show, Eq)

type EvalTStack m a = ReaderT (Env (EvalT m)) (ExceptT EvalError m) a

newtype EvalT m a = EvalT { unEvalT :: EvalTStack m a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFix
    , MonadReader (Env (EvalT m))
    , MonadError EvalError )

instance (Monad m) => MonadFail (EvalT m) where
    fail = const (throwError RuntimeError)

type Eval = EvalT Identity

runEvalT :: EvalT m a -> Env (EvalT m) -> m (Either EvalError a)
runEvalT a = runExceptT . runReaderT (unEvalT a)

runEval :: Eval a -> Env Eval -> Either EvalError a
runEval a = runIdentity . runEvalT a

evalExprT :: (Monad m, MonadFix m) => Expr -> Env (EvalT m) -> m (Either EvalError (Value (EvalT m)))
evalExprT = runEvalT . eval

evalExpr :: Expr -> Env Eval -> Either EvalError (Value Eval)
evalExpr = runEval . eval

evalMaybe :: (MonadError EvalError m) => EvalError -> Maybe (Value m) -> m (Value m)
evalMaybe err = maybe (throwError err) pure

eval
  :: (MonadFix m, MonadFail m, MonadError EvalError m, MonadReader (Env m) m)
  => Expr
  -> m (Value m)
eval = cata alg
  where
    alg :: (MonadFix m, MonadFail m, MonadError EvalError m, MonadReader (Env m) m)
        => Algebra ExprF (m (Value m))
    alg = \case
        VarS name -> do
            env <- ask
            evalMaybe (UnboundIdentifier name) (Map.lookup name env)

        LamS name expr ->
            asks (Closure name expr)

        AppS exprs ->
            foldl1 evalApp exprs

        LitS prim ->
            pure (Value prim)

        LetS var expr body -> do
            val <- expr
            local (Map.insert var val) body

        RecS var expr body -> do
            val <- mfix (\val -> local (Map.insert var val) expr)
            local (Map.insert var val) body

        IfS cond true false -> do
            Value (Bool isTrue) <- cond
            if isTrue then true else false

        MatchS expr clss -> do
            val <- expr
            evalCase val clss

        OpS op ->
            evalOp op

        AnnS expr ty ->
            expr

        ErrS ->
            throwError RuntimeError

evalCase
  :: (MonadError EvalError m, MonadReader (Env m) m)
  => Value m
  -> [(Pattern, m (Value m))]
  -> m (Value m)
evalCase _ [] = throwError RuntimeError
evalCase val ((match, expr):cs) = do
    unless (isSimple match) (throwError NonSimplePattern)
    case unfix match of
        AnyP ->
            expr

        VarP var ->
            local (Map.insert var val) expr

        con ->
            case matched con val of
                Just pairs ->
                    local (insertManyIntoEnv pairs) expr

                Nothing ->
                    evalCase val cs

insertManyIntoEnv :: [(Name, Value m)] -> Env m -> Env m
insertManyIntoEnv = flip (foldr (uncurry Map.insert))

matched :: PatternF Pattern -> Value m -> Maybe [(Name, Value m)]
matched (ConP n ps) (Data m vs) | n == m = Just (zip (getVarName <$> ps) vs)
matched _ _ = Nothing

getVarName :: Pattern -> Name
getVarName (Fix (VarP name)) = name

evalApp
  :: (MonadFail m, MonadReader (Env m) m)
  => m (Value m)
  -> m (Value m)
  -> m (Value m)
evalApp fun arg = do
    Closure var body closure <- fun
    val <- arg
    local (const (Map.insert var val closure)) body

evalOp
  :: (MonadFail m, MonadError EvalError m)
  => OpF (m (Value m))
  -> m (Value m)
evalOp = \case
    AddS a b -> numOp (+) a b
    SubS a b -> numOp (-) a b
    MulS a b -> numOp (*) a b
    DivS a b -> do
        Value v <- a
        Value w <- b
        case (v, w) of
            (Int m, Int n) ->
                int (m `div` n)

            (Float p, Float q) ->
                float (p / q)

            _ -> throwError TypeMismatch

    EqS a b  -> do
        Value val1 <- a
        Value val2 <- b
        case (val1, val2) of
            (Int m, Int n) ->
                bool (m == n)

            (Bool a, Bool b) ->
                bool (a == b)

            (Unit, Unit) ->
                bool True

            _ -> throwError TypeMismatch

    LtS a b -> do
        Value (Int m) <- a
        Value (Int n) <- b
        bool (m < n)

    GtS a b -> do
        Value (Int m) <- a
        Value (Int n) <- b
        bool (m > n)

    NegS a -> do
        Value val <- a
        case val of
            Int n ->
                int (negate n)

            Float p ->
                float (negate p)

            _ -> throwError TypeMismatch

    NotS a -> do
        Value (Bool b) <- a
        bool (not b)

    OrS a b -> do
        Value (Bool l) <- a
        Value (Bool r) <- b
        bool (l || r)

    AndS a b -> do
        Value (Bool l) <- a
        Value (Bool r) <- b
        bool (l && r)

  where
    numOp op a b = do
        Value (Int m) <- a
        Value (Int n) <- b
        int (m `op` n)

    bool  = pure . Value . Bool
    int   = pure . Value . Int
    float = pure . Value . Float
