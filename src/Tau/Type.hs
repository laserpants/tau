{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
module Tau.Type where

import Control.Monad.Except
import Data.Eq.Deriving
import Data.Function (on, (&))
import Data.Functor.Foldable
import Data.List (nub, sortOn, transpose)
import Data.Map.Strict (Map)
import Data.Set.Monad (Set, union, member, (\\))
import Data.Text (isPrefixOf)
import Data.Text.Prettyprint.Doc
import Tau.Util
import Text.Show.Deriving
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text

data TypeF  a
    = ConT Name            -- ^ Type constructor
    | VarT Name            -- ^ Type variable
    | ArrT a a             -- ^ Function type
    | AppT a a             -- ^ Type application
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Type = Fix TypeF

$(deriveShow1 ''TypeF)
$(deriveEq1   ''TypeF)

-- | Type-class constraint
data TyClass = TyCl Name Type
    deriving (Show, Eq)

-- | Type scheme (polymorphic type)
data Scheme = Forall [Name] [TyClass] Type
    deriving (Show, Eq)

data KindF a
    = VarK Name            -- ^ Kind placeholder variable
    | ArrK a a             -- ^ Type-level function
    | StarK                -- ^ Concrete type
    deriving (Show, Eq, Functor, Foldable, Traversable)

type Kind = Fix KindF

$(deriveShow1 ''KindF)
$(deriveEq1   ''KindF)

newtype Assumption a = Assumption { getAssumption :: (Name, a) }
    deriving (Show, Eq, Functor, Foldable, Traversable)

removeAssumption :: Name -> [Assumption a] -> [Assumption a]
removeAssumption var = filter ((/=) var . assumptionName)

removeManyAssumptions :: [Name] -> [Assumption a] -> [Assumption a]
removeManyAssumptions = flip (foldr removeAssumption)

assumptionName :: Assumption a -> Name
assumptionName = fst . getAssumption

-- ============================================================================
-- == Constructors
-- ============================================================================

conT :: Name -> Type
conT = Fix . ConT

varT :: Name -> Type
varT = Fix . VarT

arrT :: Type -> Type -> Type
arrT a1 a2 = Fix (ArrT a1 a2)

infixr 1 `arrT`

appT :: Type -> Type -> Type
appT a1 a2 = Fix (AppT a1 a2)

varK :: Name -> Kind
varK = Fix . VarK

arrK :: Kind -> Kind -> Kind
arrK a1 a2 = Fix (ArrK a1 a2)

starK :: Kind
starK = Fix StarK

tInt, tInteger, tBool, tFloat, tString, tChar, tUnit, tVoid :: Type

tInt     = conT "Int"      -- ^ Int
tInteger = conT "Integer"  -- ^ Integer
tBool    = conT "Bool"     -- ^ Bool
tFloat   = conT "Float"    -- ^ Float
tString  = conT "String"   -- ^ String
tChar    = conT "Char"     -- ^ Char
tUnit    = conT "Unit"     -- ^ Unit
tVoid    = conT "Void"     -- ^ Void

normalize :: Scheme -> Scheme
normalize (Forall vars tycls ty) =
    Forall (updateVar <$> vars)
           (apply sub <$> tycls)
           (apply sub ty)
  where
    updateVar v = Map.findWithDefault v v maps
    maps = Map.fromList (nub (allVars ty) `zip` letters)
    sub = Substitution (varT <$> maps)

allVars :: Type -> [Name]
allVars = cata alg where
  alg = \case
    VarT v   -> [v]
    AppT t u -> t <> u
    ArrT t u -> t <> u
    ConT{}   -> []

-- ============================================================================
-- == Substitutable
-- ============================================================================

newtype Substitution a = Substitution { getSub :: Map Name a }
    deriving (Show, Eq)

class Substitutable s t where
    apply :: Substitution s -> t -> t

subFromList :: [(Name, a)] -> Substitution a
subFromList = Substitution . Map.fromList

compose
  :: (Substitutable a a)
  => Substitution a
  -> Substitution a
  -> Substitution a
compose sub1 sub2 = Substitution sub where
    sub = Map.map (apply sub1) (getSub sub2) `Map.union` getSub sub1

mapsTo :: Name -> a -> Substitution a
mapsTo name = Substitution . Map.singleton name

substituteWithDefault :: a -> Name -> Substitution a -> a
substituteWithDefault def name = Map.findWithDefault def name . getSub

deleteFromSub :: Name -> Substitution a -> Substitution a
deleteFromSub name = Substitution . Map.delete name . getSub

deleteManyFromSub :: [Name] -> Substitution a -> Substitution a
deleteManyFromSub = flip (foldr deleteFromSub)

instance Substitutable Type Type where
    apply sub = cata alg where
        alg :: Algebra TypeF Type
        alg (VarT var)    = substituteWithDefault (varT var) var sub
        alg (ArrT t1 t2)  = arrT t1 t2
        alg (AppT t1 t2)  = appT t1 t2
        alg ty            = Fix ty

instance Substitutable Type Scheme where
    apply sub (Forall vars tycls ty) =
        Forall vars (apply sub' <$> tycls) (apply sub' ty) where
        sub' = Substitution (foldr Map.delete (getSub sub) vars)

instance Substitutable Type TyClass where
    apply sub (TyCl name ty) = TyCl name (apply sub ty)

instance (Substitutable Type t) => Substitutable Name t where
    apply = apply . Substitution . fmap varT . getSub

instance Substitutable Kind Kind where
    apply sub = cata alg where
        alg :: Algebra KindF Kind
        alg (VarK name)  = substituteWithDefault (varK name) name sub
        alg (ArrK k1 k2) = arrK k1 k2
        alg StarK        = starK

instance (Substitutable t t) => Semigroup (Substitution t) where
    (<>) = compose

instance (Substitutable t t) => Monoid (Substitution t) where
    mempty = Substitution mempty

-- ============================================================================
-- == Unifiable
-- ============================================================================

data UnificationError
    = CannotUnify
    | InfiniteType
    deriving (Show, Eq)

class Unifiable t where
    unify :: t -> t -> Either UnificationError (Substitution t)

instance Unifiable Type where
    unify = run `on` unfix where
        run (ArrT t1 t2) (ArrT u1 u2) = unifyPair (t1, t2) (u1, u2)
        run (AppT t1 t2) (AppT u1 u2) = unifyPair (t1, t2) (u1, u2)
        run (VarT a) t                = bind varT a (Fix t)
        run t (VarT a)                = bind varT a (Fix t)
        run t u                       = unifyDefault (Fix t) (Fix u)

instance Unifiable Kind where
    unify = run `on` unfix where
        run (ArrK k1 k2) (ArrK l1 l2) = unifyPair (k1, k2) (l1, l2)
        run (VarK a) k                = bind varK a (Fix k)
        run k (VarK a)                = bind varK a (Fix k)
        run k l                       = unifyDefault (Fix k) (Fix l)

unifyPair
  :: (Unifiable t, Substitutable t t)
  => (t, t)
  -> (t, t)
  -> Either UnificationError (Substitution t)
unifyPair (t1, t2) (u1, u2) = do
    sub1 <- unify t1 u1
    sub2 <- unify (apply sub1 t2) (apply sub1 u2)
    pure (sub2 <> sub1)

bind
  :: (Eq a, Free a)
  => (Name -> a)
  -> Name
  -> a
  -> Either UnificationError (Substitution a)
bind con var ty
    | con var == ty         = pure (Substitution mempty)
    | var `occursFreeIn` ty = throwError InfiniteType
    | otherwise             = pure (var `mapsTo` ty)

unifyDefault :: (Eq a) => a -> a -> Either UnificationError (Substitution a)
unifyDefault t u
    | t == u    = pure (Substitution mempty)
    | otherwise = throwError CannotUnify

-- ============================================================================
-- == Free
-- ============================================================================

class Free t where
    free :: t -> Set Name

instance (Free t) => Free [t] where
    free = foldr (union . free) mempty

instance Free Type where
    free = cata alg where
        alg (VarT var)   = Set.singleton var
        alg (ArrT t1 t2) = t1 `union` t2
        alg (AppT t1 t2) = t1 `union` t2
        alg _            = mempty

instance Free TyClass where
    free (TyCl _ ty) = free ty

instance Free Scheme where
    free (Forall vars _ ty) = free ty \\ Set.fromList vars

instance Free Kind where
    free = cata alg where
        alg (ArrK k l)  = k `union` l
        alg (VarK name) = Set.singleton name
        alg _           = mempty

occursFreeIn :: (Free t) => Name -> t -> Bool
occursFreeIn var context = var `member` free context

-- ============================================================================
-- == Active
-- ============================================================================

class Active a where
    active :: a -> Set Name

instance (Active a) => Active [a] where
    active = join . Set.fromList . fmap active

-- ============================================================================
-- == Record types
-- ============================================================================

structType :: [Name] -> [Type] -> Type
structType fields types =
    transpose [conT <$> fields', types']
        & concat
        & foldl appT (conT name)
  where
    name = "#Struct" <> intToText (length fields)
    (fields', types') = unzip (sortOn fst (zip fields types))

structFields :: Type -> Maybe [(Name, Type)]
structFields ty =
    case flatten ty of
        Fix (ConT name):rest
            | "#Struct" `isPrefixOf` name -> Just (pairUp rest)
        _ -> Nothing
  where
    pairUp (Fix (ConT k):v:t) = (k, v) : pairUp t
    pairUp _                  = []

    flatten (Fix (AppT a b))  = flatten a <> flatten b
    flatten t                 = [t]

fieldType :: Name -> Type -> Maybe Type
fieldType name ty = lookup name =<< structFields ty

-- ============================================================================
-- == Pretty Printing
-- ============================================================================

instance Pretty Type where
    pretty = cata $ \case
        ConT name -> pretty name
        VarT name -> pretty name
        ArrT a b  -> a <+> "->" <+> b
        AppT a b  -> a <+> b

instance Pretty Kind where
    pretty = cata $ \case
        VarK name -> pretty name
        ArrK a b  -> a <+> "->" <+> b
        StarK     -> "*"

instance Pretty TyClass where
    pretty (TyCl name ty) = pretty name <+> pretty ty

instance Pretty Scheme where
    pretty (Forall vars clcs ty) = forall <> classes <> pretty ty where
        forall
          | null vars = mempty
          | otherwise = "forall" <+> pretty (Text.unwords vars) <> dot <> space
        classes
          | null clcs = mempty
          | otherwise = tupled (pretty <$> clcs) <+> "=>" <> space
