{-# LANGUAGE NoMonadFailDesugaring #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad.Identity
import Control.Monad.State
import Data.HashMap.Strict (HashMap)
import Data.Set (Set)
import Data.Text (Text)
import Debug.Trace
import qualified Data.HashMap.Strict as Map
import qualified Data.Text as Text


-------------------------------------------------------------------------------
-- Name
-------------------------------------------------------------------------------

type Name = Text


type Map = HashMap


-------------------------------------------------------------------------------
-- Eval
-------------------------------------------------------------------------------

type Env = Map Name Value


emptyEnv :: Env
emptyEnv = Map.empty


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


binop :: Op -> Int -> Int -> Value
binop Add a b = VInt (a + b)
binop Mul a b = VInt (a * b)
binop Sub a b = VInt (a - b)
binop Eq a b = VBool (a == b)


eval :: Env -> Expr -> Identity Value
eval env = \case
    Var name -> do
        let Just val = Map.lookup name env
        pure val

    App fun arg -> do
        VClosure name body env1 <- eval env fun
        arg1 <- eval env arg
        eval (Map.insert name arg1 env1) body

    Lam name body ->
        pure (VClosure name body env)

    Let name expr body -> do
        expr1 <- eval env expr
        eval (Map.insert name expr1 env) body

    Lit (LInt int) ->
        pure (VInt int)

    Lit (LBool bool) ->
        pure (VBool bool)

    Fix expr ->
        eval env (App expr (Fix expr))

    If cond true false -> do
        VBool cond1 <- eval env cond
        eval env (if cond1 then true else false)

    Op op a b -> do
        VInt v1 <- eval env a
        VInt v2 <- eval env b
        pure (binop op v1 v2)


runEval :: Env -> Name -> Expr -> ( Value, Env )
runEval env name expr =
    ( val, Map.insert name val env )
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
    | Op !Op !Expr !Expr
    deriving (Show, Eq)


data Lit
    = LInt !Int
    | LBool !Bool
--    | LFloat !Double 
--    | LUnit
--    | LChar !Char
--    | LString !Text
    deriving (Show, Eq)


data Op = Add | Sub | Mul | Eq
    deriving (Show, Eq)


type Decl = ( Name, Expr )


data Program = Program ![Decl] !Expr
    deriving (Show, Eq)


-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data Type
    = TVar !Name
    | TCon !Text
    | TArr !Type !Type
    deriving (Show, Eq)


instance Substitutable Type where
    free = undefined
    apply = undefined


data Scheme = Forall ![Name] !Type
    deriving (Show, Eq)


instance Substitutable Scheme where
    free = undefined
    apply = undefined


int :: Type
int = TCon "Int"


bool :: Type
bool = TCon "Bool"


-------------------------------------------------------------------------------
-- Typing environment (TypeEnv)
-------------------------------------------------------------------------------

newtype TypeEnv = TypeEnv { types :: Map Name Scheme }
    deriving (Show, Eq)


instance Semigroup TypeEnv where
    (<>) = union


instance Monoid TypeEnv where
    mempty = emptyTypeEnv


instance Substitutable TypeEnv where
    free = undefined
    apply = undefined


emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv Map.empty


typeOf :: Name -> TypeEnv -> Maybe Scheme
typeOf name (TypeEnv env) =
    Map.lookup name env


extend :: Name -> Scheme -> TypeEnv -> TypeEnv
extend name scheme (TypeEnv env) =
    TypeEnv (Map.insert name scheme env)


remove :: Name -> TypeEnv -> TypeEnv
remove name (TypeEnv env) =
    TypeEnv (Map.delete name env)


union :: TypeEnv -> TypeEnv -> TypeEnv
union (TypeEnv a) (TypeEnv b) =
    TypeEnv (Map.union a b)


fromList :: [( Name, Scheme )] -> TypeEnv
fromList =
    TypeEnv . Map.fromList


toList :: TypeEnv -> [( Name, Scheme )]
toList (TypeEnv env) =
    Map.toList env


-------------------------------------------------------------------------------
-- Unification
-------------------------------------------------------------------------------

type Subst = Map Name Type


class Substitutable a where
    free :: a -> Set Name
    apply :: Subst -> a -> a


data InferState = InferState
    { count :: Int
    }
    deriving (Show, Eq)


type Infer a = State InferState a


getCount :: State InferState Int
getCount = do
    InferState{ count = count, .. } <- get
    put InferState{ count = count + 1, .. }
    pure count


emptySubst :: Subst
emptySubst = Map.empty


instantiate :: Scheme -> Infer Type
instantiate (Forall vars _type) = 
    undefined


generalize :: Type -> TypeEnv -> Scheme
generalize _type env =
    Forall vars _type
  where
    vars = undefined


inEnv :: Name -> Scheme -> Infer a -> Infer a
inEnv name scheme =
    undefined


infer :: Expr -> Infer Type
infer = \case
    Var name -> 
        undefined

    App fun arg -> do
        funt <- infer fun
        argt <- infer arg
        t1 <- fresh
        unify funt (TArr argt t1)
        pure t1

    Lam name body -> do
        undefined
        --t1 <- fresh
        --let tvar = Forall [] t1
        --undefined (extend name tvar)
        --t2 <- infer body
        --pure (TArr t1 t2)

    Let name expr body -> do
        t1 <- infer expr
        undefined

    Lit (LInt _ ) ->
        pure int

    Lit (LBool _) ->
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


unify :: Type -> Type -> Infer Type
unify fst snd =
    case ( fst, snd ) of
        ( TCon a, TCon b ) | a == b ->
            pure fst

        ( TArr a b, TArr a1 b1 ) -> do
            t1 <- unify a a1
            t2 <- unify b b1
            pure (TArr t1 t2)

        ( _, _ ) ->
            error "Cannot unify"


occurs = undefined


names = fmap (\c -> Text.pack [c]) ['a' .. 'z'] ++ fmap (\n -> Text.pack ('a' : show n)) [1 .. ]


fresh :: Infer Type
fresh = do
    count <- getCount
    let var = names !! count
    pure (TVar var)


-------------------------------------------------------------------------------

main :: IO ()
main =
    let
        expr1 =
            Lam "x" (Op Add (Var "x") (Lit (LInt 1)))

        expr2 =
            App expr1 (Lit (LInt 3))

        fact =
            Fix (Lam "f"
                (Lam "n"
                    (If (Op Eq (Lit (LInt 0)) (Var "n"))
                        (Lit (LInt 1))
                        (Op Mul (Var "n") (App (Var "f") (Op Sub (Var "n") (Lit (LInt 1))))))
                )
            )

        fact5 = App fact (Lit (LInt 5))

     in do
     print (eval mempty fact5)
     print (eval mempty expr1)
     print (eval mempty expr2)
