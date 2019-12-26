{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonadFailDesugaring #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Monad.Identity
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import Debug.Trace
import qualified Data.HashMap.Strict as HashMap


-------------------------------------------------------------------------------
-- Internal
-------------------------------------------------------------------------------

type Name = Text


-------------------------------------------------------------------------------
-- Eval
-------------------------------------------------------------------------------

type Env = HashMap Name Value


emptyEnv :: Env
emptyEnv = HashMap.empty


data Value
    = VInt !Int
    | VBool !Bool
    -- | VFloat !Double
    -- | VUnit
    -- | VChar !Char
    -- | VString !Text
    | VClosure !Name !Expr Env


instance Show Value where
    show (VInt n)    = show n
    show (VBool b)   = show b
    -- show (VFloat f)  = show f
    -- show (VChar c)   = show c
    -- show (VString s) = show s
    -- show VUnit       = "()"
    show VClosure{}  = "<<closure>>"


binOp :: BinOp -> Int -> Int -> Value
binOp Add a b = VInt (a + b)
binOp Mul a b = VInt (a * b)
binOp Sub a b = VInt (a - b)
binOp Eq a b = VBool (a == b)


eval :: Env -> Expr -> Identity Value
eval env = \case
    Var name -> do
        let Just val = HashMap.lookup name env
        pure val

    App fun arg -> do
        VClosure name body env1 <- eval env fun
        arg1 <- eval env arg
        eval (HashMap.insert name arg1 env1) body

    Lam name body ->
        pure (VClosure name body env)

    Let name expr body -> do
        expr1 <- eval env expr
        eval (HashMap.insert name expr1 env) body

    Lit lit ->
        case lit of
            LInt int ->
                pure (VInt int)

            LBool bool ->
                pure (VBool bool)

    Fix expr ->
        eval env (App expr (Fix expr))

    If cond true false -> do
        VBool cond1 <- eval env cond
        eval env (if cond1 then true else false)

    Op op a b -> do
        VInt v1 <- eval env a
        VInt v2 <- eval env b
        pure (binOp op v1 v2)


runEval :: Env -> Name -> Expr -> ( Value, Env )
runEval env name expr =
    ( val, HashMap.insert name val env )
  where
    val = runIdentity (eval env expr)


-------------------------------------------------------------------------------
-- Syntax (Ast)
-------------------------------------------------------------------------------

data Expr
    = Var !Name
    | App !Expr !Expr
    | Lam !Name !Expr
    | Let !Name !Expr !Expr
    | Lit !Lit
    | Fix !Expr
    | If !Expr !Expr !Expr
    | Op !BinOp !Expr !Expr
    deriving (Show, Eq)


data Lit
    = LInt !Int
    | LBool !Bool
--    | LFloat !Double 
--    | LUnit
--    | LChar !Char
--    | LString !Text
    deriving (Show, Eq)


data BinOp = Add | Sub | Mul | Eq
    deriving (Show, Eq)


-- Top-level declaration
type Decl = ( Name, Expr )


data Program = Program ![Decl] !Expr
    deriving (Show, Eq)


-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

newtype TVar = NewTVar Text
    deriving (Show, Eq)


data Type
    = TVar !TVar
    | TCon !Name
    | TArr !Type !Type
    deriving (Show, Eq)


data Scheme = Forall ![TVar] !Type
    deriving (Show, Eq)


int :: Type
int = TCon "Int"


bool :: Type
bool = TCon "Bool"


-------------------------------------------------------------------------------
-- Typing environment (TypeEnv)
-------------------------------------------------------------------------------

newtype TypeEnv = TypeEnv { types :: HashMap Name Scheme }
    deriving (Show, Eq)


newtype Unique = Unique { count :: Int }
    deriving (Show, Eq)


instance Semigroup TypeEnv where
    (<>) = union


instance Monoid TypeEnv where
    mempty = emptyTypeEnv


emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv HashMap.empty


extend :: TypeEnv -> ( Name, Scheme ) -> TypeEnv
extend (TypeEnv env) ( name, scheme ) =
    TypeEnv (HashMap.insert name scheme env)


remove :: TypeEnv -> Name -> TypeEnv
remove (TypeEnv env) name =
    TypeEnv (HashMap.delete name env)


lookup :: Name -> TypeEnv -> Maybe Scheme
lookup name (TypeEnv env) =
    HashMap.lookup name env


union :: TypeEnv -> TypeEnv -> TypeEnv
union (TypeEnv a) (TypeEnv b) =
    TypeEnv (HashMap.union a b)


fromList :: [( Name, Scheme )] -> TypeEnv
fromList xs =
    TypeEnv (HashMap.fromList xs)


toList :: TypeEnv -> [( Name, Scheme )]
toList (TypeEnv env) =
    HashMap.toList env


-------------------------------------------------------------------------------
-- Unification
-------------------------------------------------------------------------------

type Subst = HashMap TVar Type


data Matching a = Matching a


instance Functor Matching where
    fmap = undefined

instance Applicative Matching where
    (<*>) = undefined
    pure = undefined


instance Monad Matching where
    (>>=) = undefined


emptySubst :: Subst
emptySubst = HashMap.empty


infer :: Expr -> Matching Type
infer = \case
    Var name -> 
        undefined

    App fun arg -> do
        funt <- infer fun
        argt <- infer arg
        case funt of
            TArr t1 t2 -> do
                unify t1 argt
                pure t2

            _ ->
                fail "Not a function"

    Lam name body ->
        undefined

    Let name expr body -> 
        undefined

    Lit lit ->
        case lit of
            LInt _ ->
                pure int

            LBool _ ->
                pure bool

    Fix expr ->
        undefined

    If cond true false -> do
        t1 <- infer cond
        t2 <- infer true
        t3 <- infer false
        unify t1 bool
        unify t2 t3

    Op op a b -> 
        undefined


unify = undefined


occurs = undefined


-------------------------------------------------------------------------------

main :: IO ()
main =
    let
        fact =
            Fix (Lam "f"
                (Lam "n"
                    (If (Op Eq (Lit (LInt 0)) (Var "n"))
                        (Lit (LInt 1))
                        (Op Mul (Var "n") (App (Var "f") (Op Sub (Var "n") (Lit (LInt 1))))))
                )
            )

        fact5 = App fact (Lit (LInt 5))

     in print (eval mempty fact5)
