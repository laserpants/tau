{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
module Tau.Expr where

import Control.Monad.Supply
import Data.List
import Data.Text (Text)
import Data.Tuple.Extra (snd3)
import Data.Types.Injective
import Tau.Util

-- | Language primitives
data Literal
    = LUnit                   -- ^ Unit value
    | LBool Bool              -- ^ Booleans
    | LInt Int                -- ^ Bounded machine integers (32 or 64 bit)
    | LInteger Integer        -- ^ Arbitrary precision integers (bigint)
    | LFloat Double           -- ^ Floating point numbers
    | LChar Char              -- ^ Chars
    | LString Text            -- ^ Strings
    deriving (Show, Eq)

-- | Record fields
data Field t a = Field t Name a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Field
deriveEq1   ''Field

-- | Base functor for patterns
data PatternF t a
    = PVar t Name             -- ^ Variable pattern
    | PCon t Name [a]         -- ^ Constuctor pattern
    | PLit t Literal          -- ^ Literal pattern
    | PRec t [Field t a]      -- ^ Record pattern
--    | PAs  t Name a
--    | POr  t a a
    | PAny t                  -- ^ Wildcard pattern
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''PatternF
deriveEq1   ''PatternF

-- | Patterns
type Pattern t = Fix (PatternF t)

-- | Simplified patterns
data Prep t
    = RVar t Name             -- ^ Simple variable pattern
    | RCon t Name [Name]      -- ^ Simple constuctor pattern
    deriving (Show, Eq)

-- | Match expression clause
data Clause p a = Clause [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Clause
deriveEq1   ''Clause

-- | Operators
data Op a
    = OEq  a a                -- ^ Equal-to operator (==)
    | ONEq a a                -- ^ Not-equal-to operator (/=)
    | OAnd a ~a               -- ^ Logical And (&&)
    | OOr  a ~a               -- ^ Logical Or (||)
    | OAdd a a                -- ^ Addition operator (+)
    | OSub a a                -- ^ Subtraction operator (-)
    | OMul a a                -- ^ Multiplication operator (*)
    | ODiv a a                -- ^ Division operator (/)
    | OLt  a a                -- ^ Strictly less-than operator (<)
    | OGt  a a                -- ^ Strictly greater-than operator (>)
    | OLtE a a                -- ^ Less-than-or-equal-to operator (<=)
    | OGtE a a                -- ^ Greater-than-or-equal-to operator (>=)
    | ONeg a                  -- ^ Unary negation
    | ONot a                  -- ^ Logical Not
    | OIso a                  -- ^ Isomorphism operator (~)
    | OLArr a a               -- ^ Function composition operator (<<)
    | ORArr a a               -- ^ Reverse function composition (>>)               
    | OFPipe a a              -- ^ Forward pipe operator (|>)
    | OBPipe a a              -- ^ Backwards pipe operator (<|)
    | ODot Name a             -- ^ Dot operator
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Op
deriveEq1   ''Op

-- | Base functor for core language expression tree
data ExprF t p q a
    = EVar t Name             -- ^ Variable
    | ECon t Name [a]         -- ^ Constructor
    | ELit t Literal          -- ^ Literal value
    | EApp t [a]              -- ^ Function application
    | ELet t q a a            -- ^ Let-binding
    | ELam t q a              -- ^ Lambda abstraction
    | EIf  t a ~a ~a          -- ^ If-clause
    | EMat t [a] [Clause p a] -- ^ Match expression
    | EOp  t (Op a)           -- ^ Operator
    | ERec t [Field t a]      -- ^ Record
--    | EAnn u a
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

-- | Core language expression tree
type Expr t p q = Fix (ExprF t p q)

type PatternExpr t = Expr t (Pattern t) (Pattern t)

-- ////////////////////////////////////////////////////////////////////////////

class TaggedA a t where
    getTag :: a -> t
    setTag :: t -> a -> a

updateTag :: (TaggedA a t) => (t -> t) -> a -> a
updateTag f a = let tag = getTag a in setTag (f tag) a

instance TaggedA (Expr t p q) t where
    getTag = cata $ 
        \case
          EVar t _       -> t
          ECon t _ _     -> t
          ELit t _       -> t
          EApp t _       -> t
          ELet t _ _ _   -> t
          ELam t _ _     -> t
          EIf  t _ _ _   -> t
          EMat t _ _     -> t
          EOp  t _       -> t
          ERec t _       -> t
    setTag t = cata $ 
        \case
          EVar _ var     -> varExpr t var
          ECon _ con exs -> conExpr t con exs
          ELit _ lit     -> litExpr t lit
          EApp _ exs     -> appExpr t exs
          ELet _ p e1 e2 -> letExpr t p e1 e2
          ELam _ p e1    -> lamExpr t p e1
          EIf  _ c e1 e2 -> ifExpr  t c e1 e2
          EMat _ exs eqs -> matExpr t exs eqs
          EOp  _ op      -> opExpr  t op
          ERec _ fields  -> recExpr t fields

instance TaggedA (Pattern t) t where
    getTag = cata $ 
        \case
          PVar t _       -> t
          PCon t _ _     -> t
          PLit t _       -> t
          PRec t _       -> t
          PAny t         -> t
    setTag t = cata $ 
        \case
          PVar _ var     -> varPat t var
          PCon _ con ps  -> conPat t con ps
          PLit _ lit     -> litPat t lit
          PRec _ fields  -> recPat t fields
          PAny _         -> anyPat t

instance TaggedA (Prep t) t where
    getTag = 
        \case
          RVar t _       -> t
          RCon t _ _     -> t
    setTag t = 
        \case
          RVar _ var     -> RVar t var
          RCon _ con rs  -> RCon t con rs

instance TaggedA (Field t a) t where
    getTag   (Field t _ _) = t
    setTag t (Field _ n v) = Field t n v

mapTags :: (s -> t) -> Expr s (Pattern s) (Pattern s) -> Expr t (Pattern t) (Pattern t)
mapTags f = cata $ 
    \case
      EVar t var      -> varExpr (f t) var
      ECon t con exs  -> conExpr (f t) con exs
      ELit t lit      -> litExpr (f t) lit
      EApp t exs      -> appExpr (f t) exs
      ELet t p e1 e2  -> letExpr (f t) (mapPatternTags f p) e1 e2
      ELam t p e1     -> lamExpr (f t) (mapPatternTags f p) e1
      EIf  t c e1 e2  -> ifExpr  (f t) c e1 e2
      EMat t exs eqs  -> matExpr (f t) exs (clause <$> eqs)
      EOp  t op       -> opExpr  (f t) op
      ERec t fields   -> recExpr (f t) (mapField f <$> fields)
  where
    clause (Clause ps exs e) =
        Clause (mapPatternTags f <$> ps) exs e

mapPatternTags :: (s -> t) -> Pattern s -> Pattern t
mapPatternTags f = cata $ 
    \case
      PVar t var    -> varPat (f t) var
      PCon t con ps -> conPat (f t) con ps
      PLit t lit    -> litPat (f t) lit
      PRec t fields -> recPat (f t) (mapField f <$> fields)
      PAny t        -> anyPat (f t)

mapField :: (s -> t) -> Field s a -> Field t a
mapField f (Field t n v) = Field (f t) n v

fieldInfo :: Field t a -> (t, Name, a) 
fieldInfo (Field t n v) = (t, n, v)

sortFields :: [Field a c] -> [Field a c]
sortFields = sortOn (\(Field _ n _) -> n)

-- rename to fieldInfos??
sortedFields :: [Field a c] -> [(a, Name, c)]
sortedFields = (fieldInfo <$>) . sortFields

--

--getTag :: Expr t p q -> t
--getTag = cata $ \case
--    EVar t _     -> t
--    ECon t _ _   -> t
--    ELit t _     -> t
--    EApp t _     -> t
--    ELet t _ _ _ -> t
--    ELam t _ _   -> t
--    EIf  t _ _ _ -> t
--    EMat t _ _   -> t
--    EOp  t _     -> t
--
--setTag :: t -> Expr t p q -> Expr t p q
--setTag t = cata $ \case
--    EVar _ var     -> varExpr t var
--    ECon _ con exs -> conExpr t con exs
--    ELit _ lit     -> litExpr t lit
--    EApp _ exs     -> appExpr t exs
--    ELet _ p e1 e2 -> letExpr t p e1 e2
--    ELam _ p e1    -> lamExpr t p e1
--    EIf  _ c e1 e2 -> ifExpr  t c e1 e2
--    EMat _ exs eqs -> matExpr t exs eqs
--    EOp  _ op      -> opExpr  t op
--
--modifyTag :: (t -> t) -> Expr t p q -> Expr t p q
--modifyTag f p = setTag (f (getTag p)) p

--getPatternTag :: Pattern t -> t
--getPatternTag = cata $ \case
--    PVar t _   -> t
--    PCon t _ _ -> t
--    PLit t _   -> t
--    PAny t     -> t
--
--setPatternTag :: t -> Pattern t -> Pattern t
--setPatternTag t = cata $ \case
--    PVar _ var    -> varPat t var
--    PCon _ con ps -> conPat t con ps
--    PLit _ lit    -> litPat t lit
--    PAny _        -> anyPat t
--
--modifyPatternTag :: (t -> t) -> Pattern t -> Pattern t
--modifyPatternTag f p = setPatternTag (f (getPatternTag p)) p
--
--getPrepTag :: Prep t -> t
--getPrepTag = \case
--    RVar t _   -> t
--    RCon t _ _ -> t
--
--setPrepTag :: t -> Prep s -> Prep t
--setPrepTag t = \case
--    RVar _ var    -> RVar t var
--    RCon _ con rs -> RCon t con rs
--
--modifyPrepTag :: (t -> t) -> Prep t -> Prep t
--modifyPrepTag f p = setPrepTag (f (getPrepTag p)) p

--

varPat :: t -> Name -> Pattern t
varPat t var = embed (PVar t var)

conPat :: t -> Name -> [Pattern t] -> Pattern t
conPat t con ps = embed (PCon t con ps)

litPat :: t -> Literal -> Pattern t
litPat t lit = embed (PLit t lit)

recPat :: t -> [Field t (Pattern t)] -> Pattern t
recPat t fields = embed (PRec t fields)

anyPat :: t -> Pattern t
anyPat t = embed (PAny t)

varExpr :: t -> Name -> Expr t p q
varExpr t var = embed (EVar t var)

conExpr :: t -> Name -> [Expr t p q] -> Expr t p q
conExpr t con exs = embed (ECon t con exs)

litExpr :: t -> Literal -> Expr t p q
litExpr t lit = embed (ELit t lit)

appExpr :: t -> [Expr t p q] -> Expr t p q
appExpr t exs = embed (EApp t exs)

letExpr :: t -> q -> Expr t p q -> Expr t p q -> Expr t p q
letExpr t rep e1 e2 = embed (ELet t rep e1 e2)

lamExpr :: t -> q -> Expr t p q -> Expr t p q
lamExpr t rep expr = embed (ELam t rep expr)

matExpr :: t -> [Expr t p q] -> [Clause p (Expr t p q)] -> Expr t p q
matExpr t exs eqs = embed (EMat t exs eqs)

ifExpr :: t -> Expr t p q -> Expr t p q -> Expr t p q -> Expr t p q
ifExpr t cond tr fl = embed (EIf t cond tr fl)

opExpr :: t -> Op (Expr t p q) -> Expr t p q
opExpr t op = embed (EOp t op)

recExpr :: t -> [Field t (Expr t p q)] -> Expr t p q
recExpr t fs = embed (ERec t fs)

eqOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
eqOp t e1 e2 = embed (EOp t (OEq e1 e2))

andOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
andOp t e1 e2 = embed (EOp t (OAnd e1 e2))

orOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
orOp t e1 e2 = embed (EOp t (OOr e1 e2))
