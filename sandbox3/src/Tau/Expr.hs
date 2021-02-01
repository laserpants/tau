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

-- | Base functor for Pattern
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

-- | Simple patterns
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
    | OPow a a                -- ^ Exponentiation operator (^)
    | OLt  a a                -- ^ Strictly less-than operator (<)
    | OGt  a a                -- ^ Strictly greater-than operator (>)
    | OLtE a a                -- ^ Less-than-or-equal-to operator (<=)
    | OGtE a a                -- ^ Greater-than-or-equal-to operator (>=)
    | ONeg a                  -- ^ Unary negation
    | ONot a                  -- ^ Logical Not
--    | OIso a                  -- ^ Isomorphism operator (~)
    | OLArr a a               -- ^ Function composition operator (<<)
    | ORArr a a               -- ^ Reverse function composition (>>)               
    | OFPipe a a              -- ^ Forward pipe operator (|>)
    | OBPipe a a              -- ^ Backwards pipe operator (<|)
    | ODot Name a             -- ^ Dot operator
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''Op
deriveEq1   ''Op

-- | Base functor for Expr
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
--    | EFun t [Clause p a]   -- ^ Lambda-like match
--    | ELFn t Name [q] a     -- ^ Let-function expression (let f x = e) 
--    | EAnn u a
    deriving (Functor, Foldable, Traversable)

deriveShow  ''ExprF
deriveEq    ''ExprF
deriveShow1 ''ExprF
deriveEq1   ''ExprF

-- | Expression language tagged term tree
type Expr t p q = Fix (ExprF t p q)

-- | Term tree with unabridged patterns
type PatternExpr t = Expr t (Pattern t) (Pattern t)

-- | Return the precedence of a binary operator
opPrecedence :: Op a -> Int
opPrecedence = \case
    OEq    _ _ -> 4
    ONEq   _ _ -> 4    
    OAnd   _ _ -> 3   
    OOr    _ _ -> 2   
    OAdd   _ _ -> 6    
    OSub   _ _ -> 6
    OMul   _ _ -> 7
    ODiv   _ _ -> 7
    OPow   _ _ -> 8
    OLt    _ _ -> 4
    OGt    _ _ -> 4
    OLtE   _ _ -> 4    
    OGtE   _ _ -> 4
    OLArr  _ _ -> 1   
    ORArr  _ _ -> 1   
    OFPipe _ _ -> 1 
    OBPipe _ _ -> 1
    ODot   _ _ -> 0
    _          -> error "Not a binary operator"

-- | Operator associativity
data Assoc 
    = AssocL                  -- ^ Operator is left-associative 
    | AssocR                  -- ^ Operator is right-associative 
    | AssocN                  -- ^ Operator is non-associative 
    deriving (Show, Eq)

-- | Return the associativity of a binary operator
opAssoc :: Op a -> Assoc
opAssoc = \case
    OEq    _ _ -> AssocN
    ONEq   _ _ -> AssocN    
    OAnd   _ _ -> AssocR
    OOr    _ _ -> AssocR   
    OAdd   _ _ -> AssocL    
    OSub   _ _ -> AssocL
    OMul   _ _ -> AssocL
    ODiv   _ _ -> AssocL
    OPow   _ _ -> AssocR
    OLt    _ _ -> AssocN
    OGt    _ _ -> AssocN
    OLtE   _ _ -> AssocN    
    OGtE   _ _ -> AssocN
    OLArr  _ _ -> AssocR   
    ORArr  _ _ -> AssocR   
    OFPipe _ _ -> AssocL 
    OBPipe _ _ -> AssocR
    ODot   _ _ -> AssocL
    _          -> error "Not a binary operator"

exprTag :: Expr t (Pattern t) (Pattern t) -> t
exprTag = cata $ \case
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

patternTag :: Pattern t -> t
patternTag = cata $ \case
    PVar t _       -> t
    PCon t _ _     -> t
    PLit t _       -> t
    PRec t _       -> t
    PAny t         -> t

instance Injective (Field t a) (t, Name, a) where
    to (Field t n v) = (t, n, v)
