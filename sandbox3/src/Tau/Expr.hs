{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
module Tau.Expr where
-- Tau.Lang.Expr

import Control.Arrow ((>>>))
import Control.Monad.Supply
import Data.List
import Data.Text (Text)
import Data.Tuple.Extra (snd3)
import Data.Types.Injective
import Tau.Type
import Tau.Util
import qualified Data.Set.Monad as Set

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
--  | PAs  t Name a
--  | POr  t a a
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
--  | OIso a                  -- ^ Isomorphism operator (~)
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
--  | EFun t [Clause p a]     -- ^ Lambda-like match
--  | ELFn t Name [q] a       -- ^ Let-function expression (let f x = e) 
--  | EAnn Scheme a
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

exprTag :: Expr t p q -> t
exprTag = project >>> \case
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

setExprTag :: t -> Expr t p q -> Expr t p q
setExprTag t = project >>> \case
    EVar _ a       -> varExpr t a
    ECon _ a b     -> conExpr t a b
    ELit _ a       -> litExpr t a
    EApp _ a       -> appExpr t a
    ELet _ p a b   -> letExpr t p a b
    ELam _ p a     -> lamExpr t p a
    EIf  _ a b c   -> ifExpr  t a b c
    EMat _ a b     -> matExpr t a b
    EOp  _ a       -> opExpr  t a
    ERec _ s       -> recExpr t s

updateExprTag :: (t -> t) -> Expr t p q -> Expr t p q
updateExprTag update expr = setExprTag (update (exprTag expr)) expr

fieldTag :: Field t a -> t
fieldTag (Field t _ _) = t

setFieldTag :: t -> Field s a -> Field t a
setFieldTag t (Field _ n v) = Field t n v

updateFieldTag :: (t -> t) -> Field t a -> Field t a
updateFieldTag update field = setFieldTag (update (fieldTag field)) field

patternTag :: Pattern t -> t
patternTag = project >>> \case
    PVar t _       -> t
    PCon t _ _     -> t
    PLit t _       -> t
    PRec t _       -> t
    PAny t         -> t

setPatternTag :: t -> Pattern t -> Pattern t
setPatternTag t = project >>> \case
    PVar _ a       -> varPat t a
    PCon _ a b     -> conPat t a b
    PLit _ a       -> litPat t a
    PRec _ s       -> recPat t s
    PAny _         -> anyPat t

updatePatternTag :: (t -> t) -> Pattern t -> Pattern t
updatePatternTag update pat = setPatternTag (update (patternTag pat)) pat

instance Injective (Field t a) (t, Name, a) where
    to (Field t n v) = (t, n, v)

instance (Typed t) => Typed (Expr t (Pattern t) (Pattern t)) where
    typeOf = typeOf . exprTag

instance (Typed t) => Typed (Pattern t) where
    typeOf = typeOf . patternTag

fieldName :: Field t a -> Name
fieldName (Field _ n _) = n

fieldValue :: Field t a -> a
fieldValue (Field _ _ v) = v

fieldsInfo :: [Field a c] -> [(a, Name, c)]
fieldsInfo = sortOn snd3 . (to <$>)

mapTags :: (s -> t) -> PatternExpr s -> PatternExpr t 
mapTags f = cata $ \case
    EVar t a       -> varExpr (f t) a
    ECon t a b     -> conExpr (f t) a b
    ELit t a       -> litExpr (f t) a
    EApp t a       -> appExpr (f t) a
    ELet t p a b   -> letExpr (f t) (mapPatternTags f p) a b
    ELam t p a     -> lamExpr (f t) (mapPatternTags f p) a
    EIf  t a b c   -> ifExpr  (f t) a b c
    EMat t a e     -> matExpr (f t) a (clause <$> e)
    EOp  t a       -> opExpr  (f t) a
    ERec t s       -> recExpr (f t) (mapField f <$> s)
  where
    clause (Clause p a b) = Clause (mapPatternTags f <$> p) a b

mapPatternTags :: (s -> t) -> Pattern s -> Pattern t
mapPatternTags f = cata $ \case
    PVar t a       -> varPat (f t) a
    PCon t a b     -> conPat (f t) a b
    PLit t a       -> litPat (f t) a
    PRec t s       -> recPat (f t) (mapField f <$> s)
    PAny t         -> anyPat (f t)

mapField :: (s -> t) -> Field s a -> Field t a
mapField f (Field t a b) = Field (f t) a b

instance Free (Pattern t) where
    free = cata $ \case
        PVar _ name -> Set.singleton name
        PCon _ _ ps -> unions ps
        _           -> mempty

instance Free (Prep t) where
    free (RVar _ name) = Set.singleton name 
    free (RCon _ _ ns) = Set.fromList ns

varPat :: t -> Name -> Pattern t
varPat = embed2 PVar

conPat :: t -> Name -> [Pattern t] -> Pattern t
conPat = embed3 PCon

litPat :: t -> Literal -> Pattern t
litPat = embed2 PLit

recPat :: t -> [Field t (Pattern t)] -> Pattern t
recPat = embed2 PRec

anyPat :: t -> Pattern t
anyPat = embed1 PAny 

varExpr :: t -> Name -> Expr t p q
varExpr = embed2 EVar

conExpr :: t -> Name -> [Expr t p q] -> Expr t p q
conExpr = embed3 ECon 

litExpr :: t -> Literal -> Expr t p q
litExpr = embed2 ELit 

appExpr :: t -> [Expr t p q] -> Expr t p q
appExpr = embed2 EApp 

letExpr :: t -> q -> Expr t p q -> Expr t p q -> Expr t p q
letExpr = embed4 ELet 

lamExpr :: t -> q -> Expr t p q -> Expr t p q
lamExpr = embed3 ELam 

matExpr :: t -> [Expr t p q] -> [Clause p (Expr t p q)] -> Expr t p q
matExpr = embed3 EMat 

ifExpr :: t -> Expr t p q -> Expr t p q -> Expr t p q -> Expr t p q
ifExpr = embed4 EIf

recExpr :: t -> [Field t (Expr t p q)] -> Expr t p q
recExpr = embed2 ERec 

opExpr :: t -> Op (Expr t p q) -> Expr t p q
opExpr = embed2 EOp 

binOpExpr :: (a -> b -> Op (Expr t p q)) -> t -> a -> b -> Expr t p q
binOpExpr op t a b = opExpr t (op a b)

eqOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
eqOp = binOpExpr OEq 

andOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
andOp = binOpExpr OAnd 

orOp :: t -> Expr t p q -> Expr t p q -> Expr t p q
orOp = binOpExpr OOr
