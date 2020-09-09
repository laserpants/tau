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
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
module Tau.Juice where

import Control.Arrow ((<<<), (>>>), (***))
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
import Data.List (find, delete, nub)
import Data.List.Extra (groupSortOn)
import Data.Map.Strict (Map, notMember)
import Data.Set.Monad (Set, union, intersection, member, (\\))
import Data.Text (Text, pack)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Tuple.Extra (first, first3, both)
import Debug.Trace
import GHC.Show (showSpace)
import Tau.Env (Env(..))
import Text.Show.Deriving
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text (toStrict)
import qualified Tau.Env as Env

-- ============================================================================
-- =================================== Util ===================================
-- ============================================================================

type Name = Text

(#) :: a -> (a -> b) -> b
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

nameSupply :: Text -> [Name]
nameSupply prefix = (prefix <>) . Text.toStrict . toLazyText . decimal <$> [1..]

-- ============================================================================
-- =================================== Type ===================================
-- ============================================================================

data TypeF a
    = ConT Name            -- ^ Type constructor
    | VarT Name            -- ^ Type variable
    | ArrT a a             -- ^ Function type
    | AppT a a             -- ^ Type application
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1   ''TypeF)

-- | Data type that represents simple types in the target language
type Type = Fix TypeF

-- | Type-class constraint
data TyCl = TyCl Name Type
    deriving (Show, Eq)

-- | A simple type coupled with a set of type-class constraints
data ClType = ClType [TyCl] Type
    deriving (Show, Eq)

-- | Polymorphic type (referred to as type schemes in the research literature)
data Scheme = Forall [Name] [TyCl] Type
    deriving (Show, Eq)

data KindF a
    = ArrowK a a           -- ^ Type-level function
    | StarK                -- ^ Concrete type
    | VarK Name            -- ^ Kind placeholder variable
    deriving (Show, Eq, Functor)

type Kind = Fix KindF

$(deriveShow1 ''KindF)
$(deriveEq1   ''KindF)

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

tInt, tInteger, tBool, tFloat, tString, tChar, tUnit, tVoid :: Type

tInt     = conT "Int"      -- ^ Int
tInteger = conT "Integer"  -- ^ Integer
tBool    = conT "Bool"     -- ^ Bool
tFloat   = conT "Float"    -- ^ Float
tString  = conT "String"   -- ^ String
tChar    = conT "Char"     -- ^ Char
tUnit    = conT "Unit"     -- ^ Unit
tVoid    = conT "Void"     -- ^ Void

-- ============================================================================
-- =================================== Ast ====================================
-- ============================================================================

-- | Language primitives
data Prim
    = Unit                   -- ^ Unit value
    | Bool Bool              -- ^ Booleans
    | Int Int                -- ^ Machine-level integers (32 or 64 bit)
    | Integer Integer        -- ^ Arbitrary precision integers
    | Float Double           -- ^ Floating point numbers
    | Char Char              -- ^ Chars
    | String Text            -- ^ Strings
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
    | MatchS a [MatchClause a]
    | LamMatchS [MatchClause a]
    | OpS (OpF a)
    | AnnS a Scheme
    | ErrS
    deriving (Show, Eq, Functor, Foldable, Traversable)

type MatchClause a = (Pattern, a)

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
    | OrS a ~a
    | AndS a ~a
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Op = OpF (Fix ExprF)

$(deriveShow1 ''ExprF)
$(deriveEq1   ''ExprF)

$(deriveShow1 ''OpF)
$(deriveEq1   ''OpF)

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
matchS :: Expr -> [MatchClause Expr] -> Expr
matchS a = Fix . MatchS a

-- | LamMatchS constructor
lamMatchS :: [MatchClause Expr] -> Expr
lamMatchS = Fix . LamMatchS

-- | OpS constructor
opS :: OpF Expr -> Expr
opS = Fix . OpS

annS :: Expr -> Scheme -> Expr
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
-- ============================== Substitutable ===============================
-- ============================================================================

data TyCl2 a = TyCl2 Name a
    deriving (Show, Eq, Functor)

data ClType2 a = ClType2 [TyCl2 a] Type
    deriving (Show, Eq, Functor)

newtype Substitution a = Substitution { getSubstitution :: Map Name a }
    deriving (Show, Eq, Functor)

substitute :: a -> Name -> Substitution a -> a
substitute def name = Map.findWithDefault def name . getSubstitution

mapsTo :: Name -> a -> Substitution a
mapsTo name = Substitution . Map.singleton name

applySubToType :: Substitution Type -> Type -> Type
applySubToType sub = unfix >>> \case 
    VarT var   -> substitute (varT var) var sub
    ArrT t1 t2 -> arrT (applySubToType sub t1) (applySubToType sub t2)
    AppT t1 t2 -> appT (applySubToType sub t1) (applySubToType sub t2)
    ty         -> Fix ty

-- (Eq a) => a  [ a := (Show Int) => Int ]
-- applySubToClType (Substitution (Map.fromList [("a", ClType2 [TyCl2 "Show" tInt] tInt)])) (ClType2 [TyCl2 "Eq" "a"] (varT "a"))
--     -->  (Eq Int, Show Int) => Int

-- (Eq a) => a  [ a := (Show b) => b ]
-- applySubToClType (Substitution (Map.fromList [("a", ClType2 [TyCl2 "Show" (varT "b")] (varT "b"))])) (ClType2 [TyCl2 "Eq" "a"] (varT "a"))
--     -->  (Eq b, Show b) => b

-- (Eq a) => a  []
-- applySubToClType (Substitution (Map.fromList [])) (ClType2 [TyCl2 "Eq" "a"] (varT "a"))
--     -->  (Eq a) => a

applySubToTyCl :: Substitution (ClType2 Type) -> TyCl2 Name -> [TyCl2 Type]
applySubToTyCl sub (TyCl2 name var) = TyCl2 name ty : clcs where
    ClType2 clcs ty = substitute (ClType2 [] (varT var)) var sub

--xxy :: [TyCl] -> ClType -> ClType 
--xxy clcs1 (ClType clcs ty) = ClType (nub (clcs1 <> clcs)) ty

applySubToClType :: Substitution (ClType2 Type) -> ClType2 Name -> ClType2 Type
applySubToClType sub clType@(ClType2 clcs ty) = 
    case unfix ty of
        VarT var ->
            case Map.lookup var (getSubstitution sub) of
                Just (ClType2 clcs' ty') ->
                    let abc = concatMap (applySubToTyCl sub) clcs
                    in
                    ClType2 (nub (abc <> clcs')) ty'

                Nothing ->
                    ClType2 (fmap varT <$> clcs) ty

--            let ClType2 clcs' ty' = Map.findWithDefault clType var (getSubstitution sub)
--                clcs'' = concatMap (applySubToTyCl sub) clcs
--            in
--            undefined

--    case unfix ty of
--        VarT var   ->   
--          let ClType clcs' ty' = Map.findWithDefault clType var (getSubstitution sub)
--              xy3 = applySubToTyCl sub <$> clcs
--          in ClType (nub (xy3 <> clcs')) ty'
--
--          -- xxy clcs (substitute clType var sub) -- Map.findWithDefault (ClType [] (varT var)) var (getSubstitution sub) in undefined
--        ArrT t1 t2 ->
--            let xxx = applySubToClType sub (ClType [] t1)
----                yyy = applySubToClType sub t2
--             in 
--             undefined


-- (Eq a) => a  [ a := (Show Int) => Int ]
-- applySubToClType (Substitution (Map.fromList [("a", ClType [TyCl "Show" tInt] tInt)])) (ClType [TyCl "Eq" (varT "a")] (varT "a"))


-- (Eq a) => a  [ a := (Show b) => b ]
-- applySubToClType (Substitution (Map.fromList [("a", ClType [TyCl "Show" (varT "b"))] (varT "b")])) (ClType [TyCl "Eq" (varT "a")] (varT "a"))



-- instance Substitutable Type Type where
--     apply sub ty@(Fix (VarT var)) = substitute ty var sub
--     apply sub (Fix (ArrT t1 t2))  = arrT (apply sub t1) (apply sub t2)
--     apply sub (Fix (AppT t1 t2))  = appT (apply sub t1) (apply sub t2)
--     apply _ ty                    = ty

-- class Substitutable t a where
--     apply :: Substitution t -> a -> a
-- 
-- deleteFromSub :: Name -> Substitution a -> Substitution a
-- deleteFromSub name = Substitution . Map.delete name . getSubstitution
-- 
-- deleteManyFromSub :: [Name] -> Substitution a -> Substitution a
-- deleteManyFromSub = flip (foldr deleteFromSub)
-- 
-- compose
--   :: (Substitutable a a)
--   => Substitution a
--   -> Substitution a
--   -> Substitution a
-- compose sub@(Substitution map1) (Substitution map2) =
--     Substitution (Map.map (apply sub) map2 `Map.union` map1)
-- 
-- mapsTo :: Name -> a -> Substitution a
-- mapsTo name = Substitution . Map.singleton name
-- 
-- substitute :: a -> Name -> Substitution a -> a
-- substitute def name = Map.findWithDefault def name . getSubstitution
-- 
-- instance (Substitutable a a) => Semigroup (Substitution a) where
--     (<>) = compose
-- 
-- instance (Substitutable a a) => Monoid (Substitution a) where
--     mempty = Substitution mempty
-- 
-- instance (Substitutable t a) => Substitutable t [a] where
--     apply = fmap . apply
-- 
-- instance Substitutable Expr Expr where
--     apply sub = para $ \case
--         VarS var ->
--             Map.findWithDefault (varS var) var (getSubstitution sub)
-- 
--         LamS var (expr, _) ->
--             lamS var (apply (deleteFromSub var sub) expr)
-- 
--         AppS exprs ->
--             appS (snd <$> exprs)
-- 
--         LitS prim ->
--             litS prim
-- 
--         LetS var (_, body) (expr, _) ->
--             letS var body (apply (deleteFromSub var sub) expr)
-- 
--         RecS var (body, _) (expr, _) ->
--             let sub' = deleteFromSub var sub
--              in recS var (apply sub' body) (apply sub' expr)
-- 
--         IfS cond true false ->
--             ifS (snd cond) (snd true) (snd false)
-- 
--         MatchS (_, expr) clss ->
--             matchS expr (uncurry substituteClause <$> clss)
-- 
--         LamMatchS clss ->
--             lamMatchS (uncurry substituteClause <$> clss)
-- 
--         OpS op ->
--             opS (snd <$> op)
-- 
--         AnnS (_, expr) ty ->
--             annS expr ty
-- 
--       where
--         substituteClause pat (expr, _) =
--             ( pat
--             , apply (deleteManyFromSub (patternVars pat) sub) expr )
-- 
-- instance Substitutable Type Type where
--     apply sub ty@(Fix (VarT var)) = substitute ty var sub
--     apply sub (Fix (ArrT t1 t2))  = arrT (apply sub t1) (apply sub t2)
--     apply sub (Fix (AppT t1 t2))  = appT (apply sub t1) (apply sub t2)
--     apply _ ty                    = ty
-- 
-- instance Substitutable Kind Kind where
--     apply sub (Fix (VarK name))    = substitute (varK name) name sub
--     apply sub (Fix (ArrowK k1 k2)) = arrowK (apply sub k1) (apply sub k2)
--     apply _ (Fix StarK)            = starK
-- 
-- instance Substitutable Type TyCl where
--     apply sub (TyCl name ty) = TyCl name (apply sub ty)
-- 
-- -- ============================================================================
-- -- ================================= Patterns =================================
-- -- ============================================================================
-- 
-- patternVars :: Pattern -> [Name]
-- patternVars = cata alg where
--     alg :: Algebra PatternF [Name]
--     alg (VarP v)    = [v]
--     alg (ConP _ ps) = concat ps
--     alg _           = []
-- 
-- -- | Predicate to check if a pattern is /simple/. A simple pattern is
-- --     - a variable,
-- --     - a wildcard, or
-- --     - a constructor where all the subpatterns are simple.
-- --
-- isSimple :: Pattern -> Bool
-- isSimple = cata alg where
--     alg :: Algebra PatternF Bool
--     alg AnyP        = True
--     alg VarP{}      = True
--     alg (ConP _ ps) = and ps
--     alg _           = False
-- 
-- specialized :: Name -> Int -> [[Pattern]] -> [[Pattern]]
-- specialized name a = concatMap $ \(p:ps) ->
--     case unfix p of
--         ConP name' ps'
--             | name' == name -> [ps' <> ps]
--             | otherwise     -> []
-- 
--         _ ->
--             [replicate a anyP <> ps]
-- 
-- defaultMatrix :: [[Pattern]] -> [[Pattern]]
-- defaultMatrix = concatMap $ \(p:ps) ->
--     case unfix p of
--         ConP{} -> []
--         LitP{} -> []
--         _      -> [ps]
-- 
-- type ConstructorEnv = Env (Set Name)
-- 
-- constructorEnv :: [(Name, [Name])] -> ConstructorEnv
-- constructorEnv = Env.fromList . fmap (fmap Set.fromList)
-- 
-- type PatternCheckTStack m a = ReaderT ConstructorEnv m a
-- 
-- newtype PatternCheckT m a = PatternCheckT (PatternCheckTStack m a) deriving
--     ( Functor
--     , Applicative
--     , Monad
--     , MonadReader ConstructorEnv )
-- 
-- runPatternCheckT :: PatternCheckT m a -> ConstructorEnv -> m a
-- runPatternCheckT (PatternCheckT a) = runReaderT a
-- 
-- type PatternCheck = PatternCheckT Identity
-- 
-- runPatternCheck :: PatternCheck a -> ConstructorEnv -> a
-- runPatternCheck a = runIdentity . runPatternCheckT a
-- 
-- headCons :: (Monad m) => [[Pattern]] -> m [(Name, Int)]
-- headCons = fmap concat . traverse fun where
--     fun [] = error "Fatal error in pattern anomalies check"
--     fun ps = pure $ case unfix (head ps) of
--         LitP lit     -> [(prim lit, 0)]
--         ConP name rs -> [(name, length rs)]
--         _            -> []
--     prim (Bool True)  = "$True"
--     prim (Bool False) = "$False"
--     prim Unit         = "$()"
--     prim Int{}        = "$Int"
--     prim Integer{}    = "$Integer"
--     prim Float{}      = "$Float"
--     prim Char{}       = "$Char"
--     prim String{}     = "$String"
-- 
-- useful :: (MonadReader ConstructorEnv m) => [[Pattern]] -> [Pattern] -> m Bool
-- useful [] _ = pure True         -- zero rows (0x0 matrix)
-- useful px@(ps:_) qs =
--     case (qs, length ps) of
--         (_, 0) -> pure False    -- one or more rows but no columns
-- 
--         ([], _) ->
--             error "Fatal error in pattern anomalies check"
-- 
--         (Fix (ConP name rs):_, _) ->
--             let special = specialized name (length rs)
--              in useful (special px) (head (special [qs]))
-- 
--         (_:qs1, _) -> do
--             cs <- headCons px
--             isComplete <- complete (fst <$> cs)
--             if isComplete
--                 then cs & anyM (\con ->
--                     let special = uncurry specialized con
--                      in useful (special px) (head (special [qs])))
--                 else useful (defaultMatrix px) qs1
--   where
--     complete [] = pure False
--     complete names@(name:_) = do
--         defined <- ask
--         let constructors = defined `Env.union` builtIn
--         pure (Env.findWithDefaultEmpty name constructors == Set.fromList names)
-- 
--     builtIn = constructorEnv
--         [ ("$True",     ["$True", "$False"])
--         , ("$False",    ["$True", "$False"])
--         , ("$()",       ["$()"])
--         , ("$Int",      [])
--         , ("$Integer",  [])
--         , ("$Float",    [])
--         , ("$Char",     [])
--         , ("$String",   [])
--         ]
-- 
-- exhaustive :: (Monad m) => [Pattern] -> PatternCheckT m Bool
-- exhaustive ps = not <$> useful ((:[]) <$> ps) [anyP]
-- 
-- checkPatterns :: (Monad m) => ([MatchClause Bool] -> m Bool) -> Expr -> m Bool
-- checkPatterns check = cata $ \case
--     LamS _ expr ->
--         expr
-- 
--     AppS exprs ->
--         and <$> sequence exprs
-- 
--     LetS _ expr body ->
--         expr &&^ body
-- 
--     RecS _ expr body ->
--         expr &&^ body
-- 
--     IfS cond true false ->
--         cond &&^ true &&^ false
-- 
--     OpS (AddS a b) -> a &&^ b
--     OpS (SubS a b) -> a &&^ b
--     OpS (MulS a b) -> a &&^ b
--     OpS (EqS a b) -> a &&^ b
--     OpS (LtS a b) -> a &&^ b
--     OpS (GtS a b) -> a &&^ b
--     OpS (NegS a) -> a
--     OpS (NotS a) -> a
-- 
--     AnnS expr _ ->
--         expr
-- 
--     MatchS expr clss ->
--         expr &&^ (checkClauses clss >>= check)
-- 
--     LamMatchS clss ->
--         checkClauses clss >>= check
-- 
--     _ ->
--         pure True
-- 
-- checkClauses :: (Monad m) => [MatchClause (m b)] -> m [MatchClause b]
-- checkClauses clss = do
--     let (patterns, exprs) = unzip clss
--     zip patterns <$> sequence exprs
-- 
-- allPatternsAreSimple :: (Monad m) => Expr -> m Bool
-- allPatternsAreSimple = checkPatterns (pure . uncurry check . unzip) where
--     check patterns exprs =
--         and exprs &&
--         and (isSimple <$> patterns)
-- 
-- allPatternsAreExhaustive :: (Monad m) => Expr -> ConstructorEnv -> m Bool
-- allPatternsAreExhaustive =
--     runPatternCheckT . checkPatterns (exhaustive . fmap fst)
-- 
-- -- ============================================================================
-- -- ============================ Patterns Compiler =============================
-- -- ============================================================================
-- 
-- type Equation = ([Pattern], Expr)
-- 
-- data ConHead = ConHead
--     { conName  :: Name
--     , conArity :: Int
--     , conPats  :: [Pattern]
--     , conExpr  :: Expr
--     } deriving (Show, Eq)
-- 
-- data VarHead = VarHead
--     { varName  :: Maybe Name
--     , varPats  :: [Pattern]
--     , varExpr  :: Expr
--     } deriving (Show, Eq)
-- 
-- data LitHead = LitHead
--     { litPrim  :: Prim
--     , litPats  :: [Pattern]
--     , litExpr  :: Expr
--     } deriving (Show, Eq)
-- 
-- data EqGroup
--     = ConEqs [ConHead]
--     | VarEqs [VarHead]
--     | LitEqs [LitHead]
--     deriving (Show, Eq)
-- 
-- groups :: [Equation] -> [EqGroup]
-- groups qs = cs:gs
--   where
--     (cs, gs) = foldr (uncurry arrange) (ConEqs [], []) qs
-- 
--     arrange (Fix (ConP name qs):ps) expr =
--         let c = ConHead { conName  = name
--                         , conArity = length qs
--                         , conPats  = qs <> ps
--                         , conExpr  = expr }
--          in \case
--             (ConEqs cs, gs) -> (ConEqs (c:cs), gs)
--             (g, gs)         -> (ConEqs [c], g:gs)
-- 
--     arrange (Fix (VarP name):ps) expr =
--         let c = VarHead { varName = Just name
--                         , varPats = ps
--                         , varExpr = expr }
--          in \case
--             (VarEqs cs, gs) -> (VarEqs (c:cs), gs)
--             (g, gs)         -> (VarEqs [c], g:gs)
-- 
--     arrange (Fix AnyP:ps) expr =
--         let c = VarHead { varName = Nothing
--                         , varPats = ps
--                         , varExpr = expr }
--          in \case
--             (VarEqs cs, gs) -> (VarEqs (c:cs), gs)
--             (g, gs)         -> (VarEqs [c], g:gs)
-- 
--     arrange (Fix (LitP prim):ps) expr =
--         let c = LitHead { litPrim = prim
--                         , litPats = ps
--                         , litExpr = expr }
--          in \case
--             (LitEqs cs, gs) -> (LitEqs (c:cs), gs)
--             (g, gs)         -> (LitEqs [c], g:gs)
-- 
-- data ConGroup = ConGroup
--     { name      :: Name
--     , arity     :: Int
--     , equations :: [Equation]
--     } deriving (Show)
-- 
-- conGroups :: [ConHead] -> [ConGroup]
-- conGroups qs =
--     makeGroup <$> groupSortOn (\ConHead{..} -> (conName, conArity)) qs
--   where
--     makeGroup cs@(ConHead{..}:_) = ConGroup
--       { name      = conName
--       , arity     = conArity
--       , equations = (\ConHead{..} -> (conPats, conExpr)) <$> cs }
-- 
-- type PatternMatchCompilerTStack m a = SupplyT Name m a
-- 
-- newtype PatternMatchCompilerT m a = PatternMatchCompilerT
--     { unPatternMatchCompilerT :: PatternMatchCompilerTStack m a
--     } deriving (Functor, Applicative, Monad, MonadSupply Name)
-- 
-- runPatternMatchCompilerT :: (Monad m) => PatternMatchCompilerT m a -> m a
-- runPatternMatchCompilerT = flip evalSupplyT (nameSupply ":") . unPatternMatchCompilerT
-- 
-- type PatternMatchCompiler = PatternMatchCompilerT Identity
-- 
-- runPatternMatchCompiler :: PatternMatchCompiler a -> a
-- runPatternMatchCompiler = runIdentity . runPatternMatchCompilerT
-- 
-- compilePatterns :: (MonadSupply Name m) => [Expr] -> [Equation] -> m Expr
-- compilePatterns = matchDefault errS
-- 
-- matchDefault :: (MonadSupply Name m) => Expr -> [Expr] -> [Equation] -> m Expr
-- matchDefault _ [] [([], expr)] = pure expr
-- matchDefault def (u:us) qs = foldrM (flip run) def (groups qs) where
--     run :: MonadSupply Name m => Expr -> EqGroup -> m Expr
--     run def = \case
--         ConEqs eqs -> do
--             css <- traverse groupClause (conGroups eqs)
--             pure $ case css <> [(anyP, def) | errS /= def] of
--                 [] -> def
--                 css' -> matchS u css'
--           where
--             groupClause :: MonadSupply Name m => ConGroup -> m (MatchClause Expr)
--             groupClause ConGroup{..} = do
--                 vs <- replicateM arity supply
--                 expr <- matchDefault def ((varS <$> vs) <> us) equations
--                 pure (conP name (varP <$> vs), expr)
-- 
--         VarEqs eqs ->
--             matchDefault def us (fun <$> eqs) where
--                 fun VarHead{..} =
--                     ( varPats
--                     , case varName of
--                           Nothing   -> varExpr
--                           Just name -> apply (name `mapsTo` u) varExpr )
-- 
--         LitEqs eqs ->
--             foldrM fun def eqs where
--                 fun LitHead{..} false = do
--                     true <- matchDefault def us [(litPats, litExpr)]
--                     pure (ifS (eqS u (litS litPrim)) true false)
-- 
-- compileAll :: Expr -> Expr
-- compileAll = cata $ \case
--     MatchS expr clss -> run expr clss
--     LamMatchS clss   -> lamS "$" (run (varS "$") clss)
--     expr             -> Fix expr
--   where
--     run :: Expr -> [MatchClause Expr] -> Expr
--     run expr clss = first (:[]) <$> clss
--         & compilePatterns [expr]
--         & runPatternMatchCompiler
-- 
-- -- -- ============================================================================
-- -- -- ============================== Kind Inference ==============================
-- -- -- ============================================================================
-- -- 
-- -- type KindAssumption = (Name, Kind)
-- -- type KindConstraint = (Kind, Kind)
-- -- 
-- -- instance Substitutable KindConstraint KindConstraint where
-- --     apply sub = apply (fst <$> sub) *** apply (snd <$> sub)
-- -- 
-- -- runInferK :: (Monad m) => SupplyT Name m a -> m a
-- -- runInferK = flip evalSupplyT (nameSupply "")
-- -- 
-- -- inferK
-- --   :: (Monad m)
-- --   => Type
-- --   -> InferT m (Kind, [KindAssumption], [KindConstraint])
-- -- inferK = cata alg where
-- --     alg
-- --       :: (Monad m)
-- --       => Algebra TypeF (InferT m (Kind, [KindAssumption], [KindConstraint]))
-- --     alg = \case
-- --         ArrT t1 t2 -> do
-- --             (k1, as1, cs1) <- t1
-- --             (k2, as2, cs2) <- t2
-- --             pure ( starK
-- --                   , as1 <> as2
-- --                   , cs1 <> cs2 <> [(k1, starK), (k2, starK)] )
-- -- 
-- --         AppT t1 t2 -> do
-- --             (k1, as1, cs1) <- t1
-- --             (k2, as2, cs2) <- t2
-- --             kvar <- varK <$> supply
-- --             pure ( kvar
-- --                  , as1 <> as2
-- --                  , cs1 <> cs2 <> [(k1, arrowK k2 kvar)] )
-- -- 
-- --         ConT con | isPrim con ->
-- --             pure ( starK, [], [] )
-- -- 
-- --         ConT con -> assumeVar con
-- --         VarT var -> assumeVar var
-- -- 
-- --     assumeVar name = do
-- --         kvar <- varK <$> supply
-- --         pure ( kvar, [(name, kvar)], [] )
-- -- 
-- -- inferKind :: (Monad m) => Env Kind -> Type -> InferT m Kind
-- -- inferKind (Env env) ty = do
-- --     (kind, as, cs) <- inferK ty
-- --     sub <- solveKinds (cs <> envConstraints as)
-- --     pure (apply sub kind)
-- --   where
-- --     envConstraints :: [KindAssumption] -> [KindConstraint]
-- --     envConstraints as = do
-- --         (x, k) <- as
-- --         (y, l) <- Map.toList env
-- --         guard (x == y)
-- --         pure (k, l)
-- -- 
-- -- isPrim :: Name -> Bool
-- -- isPrim "Int"     = True
-- -- isPrim "Integer" = True
-- -- isPrim "Bool"    = True
-- -- isPrim "Float"   = True
-- -- isPrim "String"  = True
-- -- isPrim "Char"    = True
-- -- isPrim "Unit"    = True
-- -- isPrim "Void"    = True
-- -- isPrim _         = False
-- -- 
-- -- solveKinds :: (Monad m) => [KindConstraint] -> InferT m (Substitution Kind)
-- -- solveKinds [] = pure mempty
-- -- solveKinds ((k1, k2):cs) = do
-- --     sub1 <- liftErrors (unify k1 k2)
-- --     sub2 <- solveKinds (both (apply sub1) <$> cs)
-- --     pure (sub2 <> sub1)
-- -- 
-- -- -- ============================================================================
-- -- -- ============================== Type Inference ==============================
-- -- -- ============================================================================
-- -- 
-- -- data TypeError
-- --     = CannotSolve
-- --     | UnificationError UnificationError
-- --     | UnboundVariable Name
-- --     | EmptyMatchStatement
-- --     | ImplementationError
-- --     deriving (Show, Eq)
-- -- 
-- -- instance (Monad m) => MonadFail (InferT m) where
-- --     fail = const (throwError ImplementationError)
-- -- 
-- -- instance MonadTrans InferT where
-- --     lift = InferT . lift . lift . lift
-- -- 
-- -- type InferTStack m a = ReaderT Monoset (ExceptT TypeError (SupplyT Name m)) a
-- -- 
-- -- newtype InferT m a = InferT (InferTStack m a) deriving
-- --     ( Functor
-- --     , Applicative
-- --     , Monad
-- --     , MonadReader Monoset
-- --     , MonadSupply Name
-- --     , MonadError TypeError )
-- -- 
-- -- liftErrors :: (MonadError TypeError m) => Either UnificationError a -> m a
-- -- liftErrors = liftEither . mapLeft UnificationError
-- -- 
-- -- runInferT :: (Monad m) => InferT m a -> m (Either TypeError a)
-- -- runInferT (InferT a) =
-- --     nameSupply "a"
-- --         # Monoset mempty
-- --         & runReaderT a
-- --         & runExceptT
-- --         & evalSupplyT
-- -- 
-- -- type Infer a = InferT Identity a
-- -- 
-- -- runInfer :: Infer a -> Either TypeError a
-- -- runInfer = runIdentity . runInferT
-- -- 
-- -- -- | Monomorphic set
-- -- newtype Monoset = Monoset (Set Name)
-- --     deriving (Show, Eq)
-- -- 
-- -- insertIntoMonoset :: Name -> Monoset -> Monoset
-- -- insertIntoMonoset var (Monoset set) = Monoset (Set.insert var set)
-- -- 
-- -- insertManyIntoMonoset :: [Name] -> Monoset -> Monoset
-- -- insertManyIntoMonoset = flip (foldr insertIntoMonoset)
-- -- 
-- -- instance Free Monoset where
-- --     free (Monoset set) = set
-- -- 
-- -- instance Substitutable Type Monoset where
-- --     apply sub (Monoset set) = Monoset (free . apply sub . varT =<< set)
-- -- 
-- -- type AnnotatedAstF a = Const a :*: ExprF
-- -- 
-- -- -- | Annotated syntax tree
-- -- newtype AnnotatedAst a = AnnotatedAst
-- --     { runAnnotatedAst :: Fix (AnnotatedAstF a)
-- --     } deriving (Eq, Show)
-- -- 
-- -- instance Substitutable Type (AnnotatedAst Type) where
-- --     apply sub = runAnnotatedAst >>> cata alg >>> AnnotatedAst where
-- --         alg (Const ty :*: expr) = Fix (Const (apply sub ty) :*: expr)
-- -- 
-- -- getExpr :: AnnotatedAst a -> Expr
-- -- getExpr = cata (Fix . right) . runAnnotatedAst
-- -- 
-- -- getAnnotation :: AnnotatedAst a -> a
-- -- getAnnotation =
-- --     getConst
-- --       . left
-- --       . unfix
-- --       . runAnnotatedAst
-- -- 
-- -- infer
-- --   :: (Monad m)
-- --   => Expr
-- --   -> InferT m (AnnotatedAst Type, [Assumption], [Constraint])
-- -- infer = cata alg where
-- --     alg :: (Monad m)
-- --         => Algebra ExprF (InferT m (AnnotatedAst Type, [Assumption], [Constraint]))
-- --     alg = fmap expand >>> \case
-- --         VarS name -> do
-- --             beta <- varT <$> supply
-- --             pure ( annotated beta (VarS name)
-- --                  , [Assumption (name, beta)]
-- --                  , [] )
-- -- 
-- --         LamS name expr -> do
-- --             var <- supply
-- --             let beta = varT var
-- --             (_expr, t1, a1, c1) <- local (insertIntoMonoset var) expr
-- --             pure ( annotated (arrT beta t1) (LamS name _expr)
-- --                  , removeAssumption name a1
-- --                  , c1 <> [Equality t beta | (y, t) <- getAssumption <$> a1, name == y] )
-- -- 
-- --         AppS exprs -> do
-- --             (_expr, _, as, cs) <- foldl1 inferApp exprs
-- --             pure ( AnnotatedAst _expr, as, cs )
-- -- 
-- --         LitS prim -> do
-- --             t <- inferPrim prim
-- --             pure ( annotated t (LitS prim), [], [] )
-- -- 
-- --         LetS var expr body ->
-- --             inferLet var expr body False
-- -- 
-- --         RecS var expr body ->
-- --             inferLet var expr body True
-- -- 
-- --         IfS cond true false -> do
-- --             (_cond, t1, a1, c1) <- cond
-- --             (_true, t2, a2, c2) <- true
-- --             (_false, t3, a3, c3) <- false
-- --             pure ( annotated t2 (IfS _cond _true _false)
-- --                  , a1 <> a2 <> a3
-- --                  , c1 <> c2 <> c3 <> [Equality t1 tBool, Equality t2 t3] )
-- -- 
-- --         MatchS _ [] ->
-- --             throwError EmptyMatchStatement
-- -- 
-- --         LamMatchS [] ->
-- --             throwError EmptyMatchStatement
-- -- 
-- --         MatchS expr clss -> do
-- --             beta <- varT <$> supply
-- --             (_expr, t1, a1, c1) <- expr
-- --             (_clss, as, cs) <- foldrM (inferClause beta t1) ([], [], []) clss
-- --             pure ( annotated beta (MatchS _expr _clss)
-- --                  , a1 <> as
-- --                  , c1 <> cs )
-- -- 
-- --         LamMatchS clss -> do
-- --             beta <- varT <$> supply
-- --             zeta <- varT <$> supply
-- --             (_clss, as, cs) <- foldrM (inferClause beta zeta) ([], [], []) clss
-- --             pure ( annotated (arrT zeta beta) (LamMatchS _clss), as, cs )
-- -- 
-- --         OpS op ->
-- --             inferOp op
-- -- 
-- --         AnnS expr ty ->
-- --             undefined  -- TODO
-- -- 
-- -- inferLet
-- --   :: (MonadReader Monoset m)
-- --   => Name
-- --   -> m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --   -> m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --   -> Bool
-- --   -> m (AnnotatedAst Type, [Assumption], [Constraint])
-- -- inferLet var expr body rec = do
-- --     (_e1, t1, a1, c1) <- expr
-- --     (_e2, t2, a2, c2) <- body
-- --     set <- ask
-- --     pure ( annotated t2 ((if rec then RecS else LetS) var _e1 _e2)
-- --          , (if rec then removeAssumption var a1 else a1) <> removeAssumption var a2
-- --          , c1 <> c2 <> [Implicit t t1 set | (y, t) <- getAssumption <$> a1 <> a2, var == y] )
-- -- 
-- -- inferClause
-- --   :: (Monad m)
-- --   => Type
-- --   -> Type
-- --   -> MatchClause (InferT m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint]))
-- --   -> ([MatchClause (Fix (AnnotatedAstF Type))], [Assumption], [Constraint])
-- --   -> InferT m ([MatchClause (Fix (AnnotatedAstF Type))], [Assumption], [Constraint])
-- -- inferClause beta t (pat, expr) (ps, as, cs) = do
-- --     (_expr, t1, a1, c1) <- local (insertManyIntoMonoset vars) expr
-- --     (t2, a2, c2) <- inferPattern pat
-- --     pure ( (pat, _expr):ps
-- --          , as <> removeManyAssumptions vars a1
-- --               <> removeManyAssumptions vars a2
-- --          , cs <> c1 <> c2
-- --               <> [Equality beta t1, Equality t t2]
-- --               <> constraints a1 a2 )
-- --   where
-- --     vars = patternVars pat
-- --     constraints a1 a2 = do
-- --         (y1, t1) <- getAssumption <$> a1
-- --         (y2, t2) <- getAssumption <$> a2
-- --         var <- vars
-- --         guard (var == y1 && var == y2)
-- --         pure (Equality t1 t2)
-- -- 
-- -- inferPattern :: (Monad m) => Pattern -> InferT m (Type, [Assumption], [Constraint])
-- -- inferPattern = cata $ \case
-- --     VarP var -> do
-- --         beta <- varT <$> supply
-- --         pure (beta, [Assumption (var, beta)], [])
-- -- 
-- --     ConP name ps -> do
-- --         beta <- varT <$> supply
-- --         (ts, ass, css) <- (fmap unzip3 . sequence) ps
-- --         pure ( beta
-- --              , concat ass <> [Assumption (name, foldr arrT beta ts)]
-- --              , concat css )
-- -- 
-- --     LitP prim -> do
-- --         t <- inferPrim prim
-- --         pure (t, [], [])
-- -- 
-- --     AnyP -> do
-- --         beta <- varT <$> supply
-- --         pure (beta, [], [])
-- -- 
-- -- inferApp
-- --   :: (Monad m)
-- --   => InferT m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --   -> InferT m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --   -> InferT m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- -- inferApp fun arg = do
-- --     (_e1, t1, a1, c1) <- fun
-- --     (_e2, t2, a2, c2) <- arg
-- --     beta <- varT <$> supply
-- --     pure ( Fix (Const beta :*: AppS [_e1, _e2])
-- --          , beta
-- --          , a1 <> a2
-- --          , c1 <> c2 <> [Equality t1 (arrT t2 beta)] )
-- -- 
-- -- op1
-- --   :: (MonadSupply Name m) =>
-- --      (Fix (AnnotatedAstF Type) -> OpF (Fix (AnnotatedAstF Type)))
-- --      -> m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --      -> Scheme
-- --      -> m (AnnotatedAst Type, [Assumption], [Constraint])
-- -- op1 con e1 sig = do
-- --     (_e1, t1, a1, c1) <- e1
-- --     beta <- varT <$> supply
-- --     pure ( annotated beta (OpS (con _e1))
-- --          , a1
-- --          , c1 <> [Explicit (arrT t1 beta) sig] )
-- -- 
-- -- op2
-- --   :: (MonadSupply Name m) =>
-- --      (Fix (AnnotatedAstF Type) -> Fix (AnnotatedAstF Type) -> OpF (Fix (AnnotatedAstF Type)))
-- --      -> m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --      -> m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- --      -> Scheme
-- --      -> m (AnnotatedAst Type, [Assumption], [Constraint])
-- -- op2 con e1 e2 sig = do
-- --     (_e1, t1, a1, c1) <- e1
-- --     (_e2, t2, a2, c2) <- e2
-- --     beta <- varT <$> supply
-- --     pure ( annotated beta (OpS (con _e1 _e2))
-- --          , a1 <> a2
-- --          , c1 <> c2 <> [Explicit (arrT t1 (arrT t2 beta)) sig] )
-- -- 
-- -- inferOp
-- --   :: (Monad m)
-- --   => OpF (InferT m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint]))
-- --   -> InferT m (AnnotatedAst Type, [Assumption], [Constraint])
-- -- inferOp = \case
-- --     AddS e1 e2 -> op2 AddS e1 e2 numericOp2
-- --     SubS e1 e2 -> op2 SubS e1 e2 numericOp2
-- --     MulS e1 e2 -> op2 MulS e1 e2 numericOp2
-- --     DivS e1 e2 -> op2 DivS e1 e2 numericOp2
-- --     LtS e1 e2 -> op2 LtS e1 e2 comparisonOp
-- --     GtS e1 e2 -> op2 GtS e1 e2 comparisonOp
-- --     EqS e1 e2 -> op2 EqS e1 e2 equalityOp
-- --     NegS e -> op1 NegS e numericOp1
-- --     NotS e -> op1 NotS e numericOp1
-- --     OrS e1 e2 -> op2 OrS e1 e2 logicalOp
-- --     AndS e1 e2 -> op2 AndS e1 e2 logicalOp
-- -- 
-- -- numericOp1 :: Scheme
-- -- numericOp1 =
-- --     Forall ["a"]
-- --     [Class "Num" (varT "a")]
-- --     (arrT (varT "a") (varT "a"))
-- -- 
-- -- numericOp2 :: Scheme
-- -- numericOp2 =
-- --     Forall ["a"]
-- --     [Class "Num" (varT "a")]
-- --     (arrT (varT "a") (arrT (varT "a") (varT "a")))
-- -- 
-- -- equalityOp :: Scheme
-- -- equalityOp =
-- --     Forall ["a"]
-- --     [Class "Eq" (varT "a")]
-- --     (arrT (varT "a") (arrT (varT "a") tBool))
-- -- 
-- -- comparisonOp :: Scheme
-- -- comparisonOp =
-- --     Forall ["a"]
-- --     [Class "Ord" (varT "a")]
-- --     (arrT (varT "a") (arrT (varT "a") tBool))
-- -- 
-- -- logicalOp :: Scheme
-- -- logicalOp =
-- --     Forall []
-- --     []
-- --     (arrT tBool (arrT tBool tBool))
-- -- 
-- -- inferPrim :: (Monad m) => Prim -> InferT m Type
-- -- inferPrim = pure . \case
-- --     Unit      -> tUnit
-- --     Bool{}    -> tBool
-- --     Int{}     -> tInt
-- --     Integer{} -> tInteger
-- --     Float{}   -> tFloat
-- --     Char{}    -> tChar
-- --     String{}  -> tString
-- -- 
-- -- solveExprType
-- --   :: (Monad m)
-- --   => Env Scheme
-- --   -> Expr
-- --   -> InferT m (AnnotatedAst Type, Substitution Type, [Class])
-- -- solveExprType (Env env) expr = do
-- --     (ty, as, cs) <- infer expr
-- --     case unboundVars env as of
-- --         (var:_) ->
-- --             throwError (UnboundVariable var)
-- -- 
-- --         [] -> do
-- --             undefined
-- --             --(sub, clcs) <- runStateT (solve (cs <> envConstraints as)) []
-- --             --pure (ty, sub, clcs)
-- --   where
-- --     envConstraints :: [Assumption] -> [Constraint]
-- --     envConstraints as = do
-- --         (x, s) <- getAssumption <$> as
-- --         (y, t) <- Map.toList env
-- --         guard (x == y)
-- --         pure (Explicit s t)
-- -- 
-- -- inferType :: (Monad m) => Env Scheme -> Expr -> InferT m (AnnotatedAst Scheme)
-- -- inferType context expr = do
-- --     (ty, sub, clcs) <- solveExprType context expr
-- --     traceShowM ty
-- --     traceShowM sub
-- --     traceShowM clcs
-- --     --traceShowM (apply sub (getAnnotation ty))
-- --     --traceShowM (apply sub clcs)
-- --     annotate sub ty
-- --   where
-- --     annotate
-- --       :: (Monad m)
-- --       => Substitution Type
-- --       -> AnnotatedAst Type
-- --       -> InferT m (AnnotatedAst Scheme)
-- --     annotate sub = cata alg . runAnnotatedAst where
-- --         alg :: Monad m => Algebra (AnnotatedAstF Type) (InferT m (AnnotatedAst Scheme))
-- --         alg (Const ty :*: expr) = do
-- --             zz <- fmap runAnnotatedAst <$> sequence expr
-- --             ----pure $ annotated (generalize mempty [] (apply sub ty)) zz
-- --             pure $ annotated (generalize mempty (apply sub ty)) zz
-- -- 
-- -- --    annotate
-- -- --      :: (Monad m)
-- -- --      => Map Name Signature
-- -- --      -> AnnotatedAst Type
-- -- --      -> InferT m (AnnotatedAst Scheme)
-- -- --    annotate map = cata alg . runAnnotatedAst
-- -- --      where
-- -- --        alg
-- -- --          :: (Monad m)
-- -- --          => Algebra (AnnotatedAstF Type) (InferT m (AnnotatedAst Scheme))
-- -- --        alg (Const ty :*: expr) =
-- -- --            forall (applySigMap map [] ty) . fmap runAnnotatedAst <$> sequence expr
-- -- --        forall (clcs, ty) =
-- -- --            let
-- -- --                cod = enumFrom 1 >>= fmap (VarT . pack) . flip replicateM ['a'..'z']
-- -- --                dom = nub $ Set.toList $ free ty
-- -- --                sub = Substitution $ Map.fromList (dom `zip` cod)
-- -- --                ty' = apply sub ty
-- -- --                clcs' = filter (\(Class _ ty) -> and [var `elem` free ty' | var <- Set.toList (free ty)]) clcs
-- -- --                -- TODO --
-- -- --             in annotated $ generalize mempty (apply sub clcs') ty'
-- -- 
-- -- unboundVars :: Map Name a -> [Assumption] -> [Name]
-- -- unboundVars env as = filter (`notMember` env) (fst . getAssumption <$> as)
-- -- 
-- -- annotated :: t -> ExprF (Fix (AnnotatedAstF t)) -> AnnotatedAst t
-- -- annotated t a = AnnotatedAst $ Fix $ Const t :*: a
-- -- 
-- -- expand
-- --   :: (Monad m)
-- --   => m (AnnotatedAst Type, [Assumption], [Constraint])
-- --   -> m (Fix (AnnotatedAstF Type), Type, [Assumption], [Constraint])
-- -- expand triple = do
-- --     (e, as, cs) <- first3 runAnnotatedAst <$> triple
-- --     let Const t :*: _ = unfix e
-- --     pure (e, t, as, cs)
-- -- 
-- -- -- ============================================================================
-- -- -- ============================ Constraints Solver ============================
-- -- -- ============================================================================
-- -- 
-- -- newtype Assumption = Assumption { getAssumption :: (Name, Type) }
-- --     deriving (Show, Eq)
-- -- 
-- -- assumptionName :: Assumption -> Name
-- -- assumptionName = fst . getAssumption
-- -- 
-- -- removeAssumption :: Name -> [Assumption] -> [Assumption]
-- -- removeAssumption var = filter ((/=) var . assumptionName)
-- -- 
-- -- removeManyAssumptions :: [Name] -> [Assumption] -> [Assumption]
-- -- removeManyAssumptions = flip (foldr removeAssumption)
-- -- 
-- -- data Constraint
-- --     = Equality Type Type
-- --     | Implicit Type Type Monoset
-- --     | Explicit Type Scheme
-- --     deriving (Show, Eq)
-- -- 
-- -- instance Substitutable Type Constraint where
-- --     apply sub (Equality t1 t2)      = Equality (apply sub t1) (apply sub t2)
-- --     apply sub (Implicit t1 t2 mono) = Implicit (apply sub t1) (apply sub t2) (apply sub mono)
-- --     apply sub (Explicit t1 scheme)  = Explicit (apply sub t1) (apply sub scheme)
-- -- 
-- -- class Active a where
-- --     active :: a -> Set Name
-- -- 
-- -- instance Active Constraint where
-- --     active (Equality t1 t2)      = free t1 `union` free t2
-- --     active (Implicit t1 t2 mono) = free t1 `union` (free mono `intersection` free t2)
-- --     active (Explicit ty scheme)  = free ty `union` free scheme
-- -- 
-- -- instance (Active a) => Active [a] where
-- --     active = join . Set.fromList . fmap active
-- -- 
-- -- isSolvable :: [Constraint] -> Constraint -> Bool
-- -- isSolvable cs (Implicit _ t2 (Monoset vars)) =
-- --     Set.null (free t2 \\ vars `intersection` active cs)
-- -- isSolvable _ _ = True
-- -- 
-- -- choice :: [Constraint] -> Maybe ([Constraint], Constraint)
-- -- choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]
-- -- 
-- -- solve
-- --   :: (MonadError TypeError m, MonadSupply Name m)
-- --   => [Constraint]
-- --   -> m (Substitution (Type, [Class]))
-- -- solve [] = pure (Substitution mempty)
-- -- solve xs = maybe (throwError CannotSolve) pure (choice xs) >>= uncurry run
-- --   where
-- --     run cs = \case
-- --         Equality t1 t2 -> do
-- --             sub1 <- liftErrors (unify t1 t2)
-- --             undefined
-- -- 
-- --         Implicit t1 t2 (Monoset vars) ->
-- --             undefined
-- -- 
-- -- --    run cs = \case
-- -- --        Equality t1 t2 -> do
-- -- --            sub1 <- liftErrors (unify t1 t2)
-- -- --            modify (apply sub1)
-- -- --            sub2 <- solve (apply sub1 cs)
-- -- --            modify (apply sub2)
-- -- --            pure (sub2 <> sub1)
-- -- --
-- -- --        Implicit t1 t2 (Monoset vars) ->
-- -- --            solve (Explicit t1 (generalize vars t2):cs)
-- -- 
-- --         Explicit t1 scheme -> do
-- --             (t2, clcs) <- instantiate scheme
-- --             solve (Equality t1 t2:cs)
-- -- 
-- -- generalize :: Set Name -> Type -> Scheme
-- -- generalize vars ty = Forall (Set.toList (free ty \\ vars)) [] ty
-- -- 
-- -- instantiate :: (MonadSupply Name m) => Scheme -> m (Type, [Class])
-- -- instantiate (Forall vars clcs ty) = do
-- --     sub <- Substitution . map <$> traverse (const (varT <$> supply)) vars
-- --     pure (apply sub ty, apply sub clcs)
-- --   where
-- --     map = Map.fromList . zip vars

-- ============================================================================
-- =================================== Value ==================================
-- ============================================================================

-- | The environment is a mapping from variables to values.
type EvalEnv m = Env (Value m)

-- | An expression evaluates to a primitive value, a fully applied data
-- constructor, or a function closure.
data Value m
    = Value Prim                               -- ^ Literal value
    | Data Name [Value m]                      -- ^ Applied data constructor
    | Closure Name (m (Value m)) ~(EvalEnv m)  -- ^ Function closure

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

dataCon :: (MonadReader (EvalEnv m) m) => Name -> Int -> Value m
dataCon name 0 = Data name []
dataCon name n = Closure first val mempty
  where
    val = rest
        # init
        & foldr (\name -> asks . Closure name)

    init = do
        Env env <- ask
        let args = fmap (env Map.!) vars
        pure (Data name args)

    vars@(first:rest) = take n (nameSupply "%")

-- -- -- ============================================================================
-- -- -- ============================== Substitutable ===============================
-- -- -- ============================================================================
-- -- 
-- -- newtype Substitution a = Substitution { getSubstitution :: Map Name a }
-- --     deriving (Show, Eq, Functor)
-- -- 
-- -- class Substitutable t a where
-- --     apply :: Substitution t -> a -> a
-- -- 
-- -- deleteFromSub :: Name -> Substitution a -> Substitution a
-- -- deleteFromSub name = Substitution . Map.delete name . getSubstitution
-- -- 
-- -- deleteManyFromSub :: [Name] -> Substitution a -> Substitution a
-- -- deleteManyFromSub = flip (foldr deleteFromSub)
-- -- 
-- -- compose
-- --   :: (Substitutable a a)
-- --   => Substitution a
-- --   -> Substitution a
-- --   -> Substitution a
-- -- compose sub@(Substitution map1) (Substitution map2) =
-- --     Substitution (Map.map (apply sub) map2 `Map.union` map1)
-- -- 
-- -- sub :: Name -> a -> Substitution a
-- -- sub name = Substitution . Map.singleton name
-- -- 
-- -- instance (Substitutable a a) => Semigroup (Substitution a) where
-- --     (<>) = compose
-- -- 
-- -- instance (Substitutable a a) => Monoid (Substitution a) where
-- --     mempty = Substitution mempty
-- -- 
-- -- instance (Substitutable t a) => Substitutable t [a] where
-- --     apply = fmap . apply
-- -- 
-- -- instance Substitutable Expr Expr where
-- --     apply sub = para $ \case
-- --         VarS var ->
-- --             Map.findWithDefault (varS var) var (getSubstitution sub)
-- -- 
-- --         LamS var (expr, _) ->
-- --             lamS var (apply (deleteFromSub var sub) expr)
-- -- 
-- --         AppS exprs ->
-- --             appS (snd <$> exprs)
-- -- 
-- --         LitS prim ->
-- --             litS prim
-- -- 
-- --         LetS var (_, body) (expr, _) ->
-- --             letS var body (apply (deleteFromSub var sub) expr)
-- -- 
-- --         RecS var (body, _) (expr, _) ->
-- --             let sub' = deleteFromSub var sub
-- --              in recS var (apply sub' body) (apply sub' expr)
-- -- 
-- --         IfS cond true false ->
-- --             ifS (snd cond) (snd true) (snd false)
-- -- 
-- --         MatchS (_, expr) clss ->
-- --             matchS expr (uncurry substituteClause <$> clss)
-- -- 
-- --         LamMatchS clss ->
-- --             lamMatchS (uncurry substituteClause <$> clss)
-- -- 
-- --         OpS op ->
-- --             opS (snd <$> op)
-- -- 
-- --         AnnS (_, expr) ty ->
-- --             annS expr ty
-- -- 
-- --       where
-- --         substituteClause pat (expr, _) =
-- --             ( pat
-- --             , apply (deleteManyFromSub (patternVars pat) sub) expr )
-- -- 
-- -- instance Substitutable Type Type where
-- --     apply sub ty@(Fix (VarT var)) = Map.findWithDefault ty var (getSubstitution sub)
-- --     apply sub (Fix (ArrT t1 t2))  = arrT (apply sub t1) (apply sub t2)
-- --     apply sub (Fix (AppT t1 t2))  = appT (apply sub t1) (apply sub t2)
-- --     apply _ ty                    = ty
-- -- 
-- -- instance Substitutable Type Class where
-- --     apply sub (Class name ty) = Class name (apply sub ty)
-- -- 
-- -- instance Substitutable Type Scheme where
-- --     apply (Substitution map) (Forall vars clcs ty) =
-- --         Forall vars (apply sub clcs) (apply sub ty)
-- --       where
-- --         sub = Substitution (foldr Map.delete map vars)
-- -- 
-- -- instance Substitutable Kind Kind where
-- --     apply sub (Fix (VarK name))    = Map.findWithDefault (varK name) name (getSubstitution sub)
-- --     apply sub (Fix (ArrowK k1 k2)) = arrowK (apply sub k1) (apply sub k2)
-- --     apply _ (Fix StarK)            = starK

-- ============================================================================
-- =================================== Free ===================================
-- ============================================================================

-- | Class of types that may contain free type variables
class Free t where
    free :: t -> Set Name

instance (Free t) => Free [t] where
    free = foldr (union . free) mempty

instance Free Type where
    free (Fix (VarT var))   = Set.singleton var
    free (Fix (ArrT t1 t2)) = free t1 `union` free t2
    free (Fix (AppT t1 t2)) = free t1 `union` free t2
    free _                  = mempty

instance Free ClType where
    free (ClType _ ty) = free ty

instance Free Scheme where
    free (Forall vars _ ty) = free ty \\ Set.fromList vars

instance (Free a) => Free (Env a) where
    free = free . Env.elems

instance Free TyCl where 
    free (TyCl _ ty) = free ty

instance Free Kind where
    free (Fix (ArrowK k l)) = free k `union` free l
    free (Fix (VarK name))  = Set.singleton name
    free _                  = mempty

occursFreeIn :: (Free t) => Name -> t -> Bool
occursFreeIn var context = var `member` free context

-- -- ============================================================================
-- -- =================================== Eval ===================================
-- -- ============================================================================
-- 
-- data EvalError
--     = RuntimeError
--     | UnboundIdentifier Name
--     | NonSimplePattern
--     | TypeMismatch
--     deriving (Show, Eq)
-- 
-- type EvalTStack m a = ReaderT (EvalEnv (EvalT m)) (ExceptT EvalError m) a
-- 
-- newtype EvalT m a = EvalT { unEvalT :: EvalTStack m a } deriving
--     ( Functor
--     , Applicative
--     , Monad
--     , MonadFix
--     , MonadReader (EvalEnv (EvalT m))
--     , MonadError EvalError )
-- 
-- instance (Monad m) => MonadFail (EvalT m) where
--     fail = const (throwError RuntimeError)
-- 
-- type Eval = EvalT Identity
-- 
-- runEvalT :: EvalT m a -> EvalEnv (EvalT m) -> m (Either EvalError a)
-- runEvalT a = runExceptT . runReaderT (unEvalT a)
-- 
-- runEval :: Eval a -> EvalEnv Eval -> Either EvalError a
-- runEval a = runIdentity . runEvalT a
-- 
-- evalExprT :: (Monad m, MonadFix m) => Expr -> EvalEnv (EvalT m) -> m (Either EvalError (Value (EvalT m)))
-- evalExprT = runEvalT . eval
-- 
-- evalExpr :: Expr -> EvalEnv Eval -> Either EvalError (Value Eval)
-- evalExpr = runEval . eval
-- 
-- evalMaybe :: (MonadError EvalError m) => EvalError -> Maybe (Value m) -> m (Value m)
-- evalMaybe err = maybe (throwError err) pure
-- 
-- evalVar :: (MonadError EvalError m, MonadReader (EvalEnv m) m) => Name -> m (Value m)
-- evalVar name = do
--     env <- ask
--     evalMaybe (UnboundIdentifier name) (Env.lookup name env)
-- 
-- eval
--   :: (MonadFix m, MonadFail m, MonadError EvalError m, MonadReader (EvalEnv m) m)
--   => Expr
--   -> m (Value m)
-- eval = cata alg
--   where
--     alg :: (MonadFix m, MonadFail m, MonadError EvalError m, MonadReader (EvalEnv m) m)
--         => Algebra ExprF (m (Value m))
--     alg = \case
--         VarS name ->
--             evalVar name
-- 
--         LamS name expr ->
--             asks (Closure name expr)
-- 
--         AppS exprs ->
--             foldl1 evalApp exprs
-- 
--         LitS prim ->
--             pure (Value prim)
-- 
--         LetS var expr body -> do
--             val <- expr
--             local (Env.insert var val) body
-- 
--         RecS var expr body -> do
--             val <- mfix (\val -> local (Env.insert var val) expr)
--             local (Env.insert var val) body
-- 
--         IfS cond true false -> do
--             Value (Bool isTrue) <- cond
--             if isTrue then true else false
-- 
--         MatchS expr clss ->
--             expr >>= evalMatch clss
-- 
--         LamMatchS clss ->
--             asks (Closure "$" (evalVar "$" >>= evalMatch clss))
-- 
--         OpS op ->
--             evalOp op
-- 
--         AnnS expr ty ->
--             expr
-- 
--         ErrS ->
--             throwError RuntimeError
-- 
-- evalMatch
--   :: (MonadError EvalError m, MonadReader (EvalEnv m) m)
--   => [MatchClause (m (Value m))]
--   -> Value m
--   -> m (Value m)
-- evalMatch [] _ = throwError RuntimeError
-- evalMatch ((match, expr):cs) val = do
--     unless (isSimple match) (throwError NonSimplePattern)
--     case unfix match of
--         AnyP ->
--             expr
-- 
--         VarP var ->
--             local (Env.insert var val) expr
-- 
--         con ->
--             case matched con val of
--                 Just pairs ->
--                     local (Env.insertMany pairs) expr
-- 
--                 Nothing ->
--                     evalMatch cs val
-- 
-- matched :: PatternF Pattern -> Value m -> Maybe [(Name, Value m)]
-- matched (ConP n ps) (Data m vs) | n == m = Just (zip (getVarName <$> ps) vs)
-- matched _ _ = Nothing
-- 
-- getVarName :: Pattern -> Name
-- getVarName (Fix (VarP name)) = name
-- 
-- evalApp
--   :: (MonadFail m, MonadReader (EvalEnv m) m)
--   => m (Value m)
--   -> m (Value m)
--   -> m (Value m)
-- evalApp fun arg = do
--     Closure var body (Env closure) <- fun
--     val <- arg
--     local (const (Env (Map.insert var val closure))) body
-- 
-- evalOp
--   :: (MonadFail m, MonadError EvalError m)
--   => OpF (m (Value m))
--   -> m (Value m)
-- evalOp = \case
--     AddS a b -> numOp (+) a b
--     SubS a b -> numOp (-) a b
--     MulS a b -> numOp (*) a b
--     DivS a b -> do
--         Value v <- a
--         Value w <- b
--         case (v, w) of
--             (Int m, Int n) ->
--                 int (m `div` n)
-- 
--             (Float p, Float q) ->
--                 float (p / q)
-- 
--             _ -> throwError TypeMismatch
-- 
--     EqS a b  -> do
--         Value val1 <- a
--         Value val2 <- b
--         case (val1, val2) of
--             (Int m, Int n) ->
--                 bool (m == n)
-- 
--             (Bool a, Bool b) ->
--                 bool (a == b)
-- 
--             (Unit, Unit) ->
--                 bool True
-- 
--             _ -> throwError TypeMismatch
-- 
--     LtS a b -> do
--         Value (Int m) <- a
--         Value (Int n) <- b
--         bool (m < n)
-- 
--     GtS a b -> do
--         Value (Int m) <- a
--         Value (Int n) <- b
--         bool (m > n)
-- 
--     NegS a -> do
--         Value val <- a
--         case val of
--             Int n ->
--                 int (negate n)
-- 
--             Float p ->
--                 float (negate p)
-- 
--             _ -> throwError TypeMismatch
-- 
--     NotS a -> do
--         Value (Bool b) <- a
--         bool (not b)
-- 
--     OrS a b -> do
--         Value (Bool l) <- a
--         Value (Bool r) <- b
--         bool (l || r)
-- 
--     AndS a b -> do
--         Value (Bool l) <- a
--         Value (Bool r) <- b
--         bool (l && r)
-- 
--   where
--     numOp op a b = do
--         Value (Int m) <- a
--         Value (Int n) <- b
--         int (m `op` n)
-- 
--     bool  = pure . Value . Bool
--     int   = pure . Value . Int
--     float = pure . Value . Float

-- ============================================================================
-- ==============================  Unification  ===============================
-- ============================================================================

data UnificationError
    = CannotUnify
    | InfiniteType
    deriving (Show, Eq)

unifyTypes :: (MonadError UnificationError m) => Type -> Type -> m (Substitution Type)
unifyTypes t u = case (unfix t, unfix u) of
    (ArrT t1 t2, ArrT u1 u2) -> unifyTypePair (t1, t2) (u1, u2)
    (AppT t1 t2, AppT u1 u2) -> unifyTypePair (t1, t2) (u1, u2)
    (VarT a, t)              -> bind a (Fix t)
    (t, VarT a)              -> bind a (Fix t)
    (t, u) | t == u          -> pure (Substitution mempty)
           | otherwise       -> throwError CannotUnify

bind :: (MonadError UnificationError m) => Name -> Type -> m (Substitution Type)
bind var ty
    | varT var == ty        = pure (Substitution mempty)
    | var `occursFreeIn` ty = throwError InfiniteType
    | otherwise             = pure (var `mapsTo` ty)

compose :: Substitution Type -> Substitution Type -> Substitution Type
compose sub@(Substitution map1) (Substitution map2) =
    Substitution (Map.map (applySubToType sub) map2 `Map.union` map1)

unifyTypePair :: (MonadError UnificationError m) => (Type, Type) -> (Type, Type) -> m (Substitution Type)
unifyTypePair (t1, t2) (u1, u2) = do
    sub1 <- unifyTypes t1 u1
    sub2 <- unifyTypes (applySubToType sub1 t2) (applySubToType sub1 u2)
    pure (sub2 `compose` sub1)

unifyClTypes :: (MonadError UnificationError m) => ClType2 t -> ClType2 t -> m (Substitution (ClType2 t))
unifyClTypes (ClType2 clcs1 t1) (ClType2 clcs2 t2) = do
    undefined
--    sub <- unifyTypes t1 t2
--    pure (liftSub (nub (clcs2 <> clcs1)) sub)

-- composeClType :: Substitution ClType -> Substitution ClType -> Substitution ClType
-- composeClType sub@(Substitution map1) (Substitution map2) =
--     Substitution (Map.map (applySubToClType sub) map2 `Map.union` map1)
-- 
-- unifyClTypes :: (MonadError UnificationError m) => ClType -> ClType -> m (Substitution ClType)
-- unifyClTypes (ClType clcs1 t1) (ClType clcs2 t2) = do
--     sub <- unifyTypes t1 t2
--     pure (liftSub (nub (clcs2 <> clcs1)) sub)
-- 
-- liftSub :: [TyCl] -> Substitution Type -> Substitution ClType
-- liftSub clcs = Substitution . Map.mapWithKey fun . getSubstitution
--   where
--     fun :: Name -> Type -> ClType
--     fun name = ClType (filter (elem name . free) clcs)


-- class Unifiable t where
--     unify :: t -> t -> Either UnificationError (Substitution t)
--     same :: Name -> t -> Bool
-- 
-- -- | Types are unifiable
-- instance Unifiable Type where
--     unify (Fix (ArrT t1 t2)) (Fix (ArrT u1 u2)) = unifyPair (t1, t2) (u1, u2)
--     unify (Fix (AppT t1 t2)) (Fix (AppT u1 u2)) = unifyPair (t1, t2) (u1, u2)
--     unify (Fix (VarT a)) t = bind a t
--     unify t (Fix (VarT a)) = bind a t
--     unify t u = unifyDefault t u
--     same name ty = varT name == ty
-- 
-- instance Unifiable ClType where
--     unify = unifyClType 
--     same name (ClType _ ty) = varT name == ty
-- 
-- unifyClType :: ClType -> ClType -> Either UnificationError (Substitution ClType)
-- unifyClType (ClType clcs1 (Fix (ArrT t1 t2))) (ClType clcs2 (Fix (ArrT u1 u2))) = do
--     sub1 <- unify t1 u1
--     sub2 <- unify (apply sub1 t2) (apply sub1 u2)
--     --let sub = sub2 <> sub1
--     --let clcs = apply sub (clcs1 <> clcs2)
--     --pure (sub2 <> sub1)
--     pure (composeX (clcs2 <> clcs1) sub2 sub1)
-- 
-- composeX :: [TyCl] -> Substitution Type -> Substitution Type -> Substitution ClType
-- composeX = undefined
-- 
-- --compose
-- --  :: (Substitutable a a)
-- --  => Substitution a
-- --  -> Substitution a
-- --  -> Substitution a
-- --compose sub@(Substitution map1) (Substitution map2) =
-- --    Substitution (Map.map (apply sub) map2 `Map.union` map1)
-- 
-- -- | Kinds are unifiable
-- instance Unifiable Kind where
--     unify (Fix (ArrowK k1 k2)) (Fix (ArrowK l1 l2)) = unifyPair (k1, k2) (l1, l2)
--     unify (Fix (VarK a)) k = bind a k
--     unify k (Fix (VarK a)) = bind a k
--     unify k l = unifyDefault k l
--     same name k = varK name == k
-- 
-- unifyPair
--   :: (Unifiable a, Substitutable a a)
--   => (a, a)
--   -> (a, a)
--   -> Either UnificationError (Substitution a)
-- unifyPair (t1, t2) (u1, u2) = do
--     sub1 <- unify t1 u1
--     sub2 <- unify (apply sub1 t2) (apply sub1 u2)
--     pure (sub2 <> sub1)
-- 
-- unifyDefault
--   :: (Unifiable a, Substitutable a a, Eq a)
--   => a
--   -> a
--   -> Either UnificationError (Substitution a)
-- unifyDefault t u
--     | t == u    = pure mempty
--     | otherwise = throwError CannotUnify
-- 
-- bind
--   :: (Unifiable a, Free a, Substitutable a a, Eq a)
--   => Name
--   -> a
--   -> Either UnificationError (Substitution a)
-- bind var ty
--     | same var ty            = pure mempty
--     | var `occursFreeIn` ty = throwError InfiniteType
--     | otherwise             = pure (var `mapsTo` ty)
-- 
-- -- ============================================================================
-- -- ============================== Type Inference ==============================
-- -- ============================================================================
-- 
-- data TypeError
--     = CannotSolve
--     | UnificationError UnificationError
--     | UnboundVariable Name
--     | EmptyMatchStatement
--     | ImplementationError
--     deriving (Show, Eq)
-- 
-- instance (Monad m) => MonadFail (InferT m) where
--     fail = const (throwError ImplementationError)
-- 
-- instance MonadTrans InferT where
--     lift = InferT . lift . lift . lift
-- 
-- type InferTStack m a = ReaderT Monoset (ExceptT TypeError (SupplyT Name m)) a
-- 
-- newtype InferT m a = InferT (InferTStack m a) deriving
--     ( Functor
--     , Applicative
--     , Monad
--     , MonadReader Monoset
--     , MonadSupply Name
--     , MonadError TypeError )
-- 
-- liftErrors :: (MonadError TypeError m) => Either UnificationError a -> m a
-- liftErrors = liftEither . mapLeft UnificationError
-- 
-- runInferT :: (Monad m) => InferT m a -> m (Either TypeError a)
-- runInferT (InferT a) =
--     nameSupply "a"
--         # Monoset mempty
--         & runReaderT a
--         & runExceptT
--         & evalSupplyT
-- 
-- type Infer a = InferT Identity a
-- 
-- runInfer :: Infer a -> Either TypeError a
-- runInfer = runIdentity . runInferT
-- 
-- -- | Monomorphic set
-- newtype Monoset = Monoset (Set Name)
--     deriving (Show, Eq)
-- 
-- instance Free Monoset where
--     free (Monoset set) = set
-- 
-- -- ============================================================================
-- -- ========================== Type Constraints Solver =========================
-- -- ============================================================================
-- 
-- newtype Assumption = Assumption { getAssumption :: (Name, Type) }
--     deriving (Show, Eq)
-- 
-- data Constraint
--     = Equality Type Type [TyCl]
--     | Implicit Type Type Monoset
--     | Explicit ClType Scheme
--     deriving (Show, Eq)
-- 
-- class Active a where
--     active :: a -> Set Name
-- 
-- instance (Active a) => Active [a] where
--     active = join . Set.fromList . fmap active
-- 
-- instance Active Constraint where
--     active (Equality t1 t2 _)    = free t1 `union` free t2
--     active (Implicit t1 t2 mono) = free t1 `union` (free mono `intersection` free t2)
--     active (Explicit ty scheme)  = free ty `union` free scheme
-- 
-- isSolvable :: [Constraint] -> Constraint -> Bool
-- isSolvable cs (Implicit _ t2 (Monoset vars)) =
--     Set.null (free t2 \\ vars `intersection` active cs)
-- isSolvable _ _ = True
-- 
-- choice :: [Constraint] -> Maybe ([Constraint], Constraint)
-- choice xs = find (uncurry isSolvable) [(ys, x) | x <- xs, let ys = delete x xs]
-- 
-- solve
--   :: (MonadError TypeError m, MonadSupply Name m)
--   => [Constraint]
--   -> m (Substitution ClType)
-- solve [] = pure (Substitution mempty)
-- solve xs = maybe (throwError CannotSolve) pure (choice xs) >>= uncurry run
--   where
--     run cs = \case
--         Equality t1 t2 clcs -> do
--             sub1 <- liftErrors (unify (ClType [] t1) (ClType clcs t2))
--             undefined
-- 
-- --        Implicit t1 t2 (Monoset vars) ->
-- --            undefined
-- --
-- ----    run cs = \case
-- ----        Equality t1 t2 -> do
-- ----            sub1 <- liftErrors (unify t1 t2)
-- ----            modify (apply sub1)
-- ----            sub2 <- solve (apply sub1 cs)
-- ----            modify (apply sub2)
-- ----            pure (sub2 <> sub1)
-- ----
-- ----        Implicit t1 t2 (Monoset vars) ->
-- ----            solve (Explicit t1 (generalize vars t2):cs)
-- --
-- --        Explicit t1 scheme -> do
-- --            (t2, clcs) <- instantiate scheme
-- --            solve (Equality t1 t2:cs)
-- --
-- generalize :: Set Name -> Type -> Scheme
-- generalize vars ty = Forall (Set.toList (free ty \\ vars)) [] ty
-- 
-- instantiate :: (MonadSupply Name m) => Scheme -> m (Type, [TyCl])
-- instantiate (Forall vars clcs ty) = do
--     sub <- Substitution . map <$> traverse (const (varT <$> supply)) vars
--     pure (apply sub ty, apply sub clcs)
--   where
--     map = Map.fromList . zip vars
