{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Expr where

import Tau.Type
import Tau.Util

data Literal
    = LUnit
    | LBool Bool
    | LInt Int
    deriving (Show, Eq)

data PatternF t a
    = PVar t Name                 
    | PCon t Name [a]
    | PLit t Literal              
    | PAny t                     
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''PatternF
deriveEq1   ''PatternF

type Pattern t = Fix (PatternF t)

data RepF a
    = RVar Name                 
    | RCon Name [a]
--    | RCon Name Scheme [a]
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''RepF
deriveEq1   ''RepF

type Rep = Fix RepF

type SimpleRep = RepF Name

--data ExprF t p a
data ExprF t a
    = EVar t Name
    | ELit t Literal
    | EApp t [a]
    | ELet t Rep a a
    | ELam t Rep a
--    | EMatch 
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''ExprF
deriveEq1   ''ExprF

--type Expr t p = Fix (ExprF t p)
type Expr t = Fix (ExprF t)

data EquationF p a = EquationF [p] [a] a
    deriving (Show, Eq, Functor, Foldable, Traversable)

deriveShow1 ''EquationF
deriveEq1   ''EquationF

type Equation t p = EquationF p (Expr t)

getTag :: Expr t -> t
getTag = cata $ \case
    EVar t _     -> t
    ELit t _     -> t
    EApp t _     -> t
    ELet t _ _ _ -> t
    ELam t _ _   -> t

pvar :: Name -> Pattern t
pvar a1 = Fix (PVar a1)

pcon :: Name -> [Pattern] -> Pattern
pcon a1 a2 = Fix (PCon a1 a2)

plit :: Literal -> Pattern
plit a1 = Fix (PLit a1)

pany :: Pattern
pany = Fix PAny

--rvar :: Name -> Rep t
--rvar a1 = Fix (RVar a1)
--
--rcon :: Name -> [Rep t] -> Rep t
--rcon a1 a2 = Fix (RCon a1 a2)

--svar :: Name -> SimpleRep t
--svar a1 = RVar a1
--
--scon :: Name -> [Name] -> SimpleRep t
--scon a1 a2 = RCon a1 a2 

--evar :: Name -> Expr () p
evar a1 = Fix (EVar () a1)

--tagVar :: t -> Name -> Expr t p
tagVar t a1 = Fix (EVar t a1)
--
--elit :: Literal -> Expr () p 
elit a1 = Fix (ELit () a1)
--
--tagLit :: t -> Literal -> Expr t p 
tagLit t a1 = Fix (ELit t a1)
-- 
-- eapp :: [Expr () p] -> Expr () p
eapp a1 = Fix (EApp () a1)
-- 
-- tagApp :: t -> [Expr t p] -> Expr t p
tagApp t a1 = Fix (EApp t a1)
-- 
-- elet :: p -> Expr () p -> Expr () p -> Expr () p 
elet a1 a2 a3 = Fix (ELet () a1 a2 a3)
-- 
-- tagLet :: t -> p -> Expr t p -> Expr t p -> Expr t p 
tagLet t a1 a2 a3 = Fix (ELet t a1 a2 a3)
-- 
-- elam :: p -> Expr () p -> Expr () p 
elam a1 a2 = Fix (ELam () a1 a2)
-- 
-- tagLam :: t -> p -> Expr t p -> Expr t p 
tagLam t a1 a2 = Fix (ELam t a1 a2)
-- 
-- eif = undefined
-- 
-- tagIf = undefined
-- 
-- eand = undefined
-- 
-- tagAnd = undefined
-- 
-- eerr = undefined
-- 
-- eunit :: Expr () p
-- eunit = elit LUnit
-- 
-- ebool :: Bool -> Expr () p
-- ebool a1 = elit (LBool a1)
-- 
-- eint :: Int -> Expr () p
-- eint a1 = elit (LInt a1)
