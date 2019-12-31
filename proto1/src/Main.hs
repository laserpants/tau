{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonadFailDesugaring #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import Data.Set (Set, difference, member, union)
import Data.Text (Text)
import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text


-------------------------------------------------------------------------------
-- Var
-------------------------------------------------------------------------------

type Var = Text


class Free a where
    free :: a -> Set Var


instance Free a => Free [a] where
    free = foldr (union . free) Set.empty


-------------------------------------------------------------------------------
-- Eval
-------------------------------------------------------------------------------

type Env = Map Var Value


type Eval = Reader Env


emptyEnv :: Env
emptyEnv = Map.empty


data Value 
    = Int !Integer 
    | Bool !Bool
    -- | Int32 !Int32
    -- | Int64 !Int64
    -- | Float !Double
    -- | Unit
    -- | Char !Char
    -- | String !Text
    | Closure !Var !Expr Env
    deriving (Eq)


instance Show Value where
    show (Int n)    = show n
    show (Bool b)   = show b
    -- show (VFloat f)  = show f
    -- show (VChar c)   = show c
    -- show (VString s) = show s
    -- show VUnit       = "()"
    show Closure{}  = "<<closure>>"


binop :: Op -> Integer -> Integer -> Value
binop Add a b = Int (a + b)
binop Mul a b = Int (a * b)
binop Sub a b = Int (a - b)
binop Eq a b = Bool (a == b)


eval :: Expr -> Eval Value
eval = \case 
    Var name -> do
        Just val <- asks $ Map.lookup name
        pure val

    App fun arg -> do
        Closure name body env <- eval fun
        arg' <- eval arg
        let env' = Map.insert name arg' env
        local (const env') (eval body)

    Lam name body -> do
        env <- ask 
        pure (Closure name body env)

    Let name expr body -> 
        eval (App (Lam name body) expr)

    Lit val ->
        pure val

    Fix expr ->
        eval (App expr (Fix expr))

    If cond true false -> do
        Bool cond' <- eval cond
        eval (if cond' then true else false)

    Op op a b -> do
        Int a' <- eval a
        Int b' <- eval b
        pure (binop op a' b')


runEval :: Env -> Var -> Expr -> ( Value, Env )
runEval env name expr =
    ( val, Map.insert name val env )
  where
    val = runReader (eval expr) env


-------------------------------------------------------------------------------
-- Syntax (Ast)
-------------------------------------------------------------------------------

data Expr
    = Var !Var
    | App !Expr !Expr
    | Lam !Var !Expr
    | Let !Var !Expr !Expr
    | Lit !Value
    | Fix !Expr
    | If !Expr !Expr !Expr
    | Op !Op !Expr !Expr
    deriving (Show, Eq)


data Op = Add | Sub | Mul | Eq
    deriving (Show, Eq, Ord)


data Program = Program !(Map Var Expr) !Expr
    deriving (Show, Eq)


-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data Type
    = TVar !Var
--    | EVar !Int
--    | TCon !Text
    | TInt
    | TBool
    | TArr !Type !Type
    deriving (Show, Eq, Ord)


instance Free Type where
    free (TVar name)  = Set.singleton name
    free (TArr t1 t2) = free t1 `union` free t2
    free _            = Set.empty


data Scheme = Forall !(Set Var) !Type
    deriving (Show, Eq)


instance Free Scheme where
    free (Forall vars tau) = free tau `difference` vars


---------------------------------------------------------------------------------
---- Typing environment (Context)
---------------------------------------------------------------------------------

newtype Context = Context (Map Var Scheme)
    deriving (Show, Eq)


instance Free Context where
    free (Context env) = foldr (Set.union . free) (Set.empty) (Map.elems env)


extend :: Var -> Scheme -> Context -> Context 
extend name scheme (Context env) =
    Context (Map.insert name scheme env)


apply1 :: Sub -> Context -> Context
apply1 sub (Context env) = 
    Context (Map.map fun env)
  where
    fun (Forall vars tau) = Forall vars (apply sub' tau)
      where
        sub' = foldr Map.delete sub vars


---------------------------------------------------------------------------------
---- Unification
---------------------------------------------------------------------------------

data UniState = UniState
    { count :: Int
    }
    deriving (Show, Eq, Ord)


newUniState :: UniState
newUniState = UniState { count = 0 }


counterStep :: State UniState Int
counterStep = do
    UniState{ count = count, .. } <- get
    put UniState{ count = count + 1, .. }
    pure count


type Unify = State UniState


type Sub = Map Var Type


instantiate :: Scheme -> Unify Type
instantiate (Forall vars tau) = do
    vars' <- mapM (const fresh) varsL
    pure $ apply (Map.fromList (varsL `zip` vars')) tau
  where
    varsL = Set.toList vars


generalize :: Context -> Type -> Scheme
generalize context tau =
    Forall (free tau `difference` free context) tau


substitute :: Var -> Type -> Sub
substitute = Map.singleton


compose :: Sub -> Sub -> Sub
compose sub1 sub2 = 
    Map.map (apply sub1) sub2 `Map.union` sub1


infer :: Context -> Expr -> Unify ( Sub, Type )
infer context = \case
    Var name -> 
        let 
            Context env = context
        in
        case Map.lookup name env of
            Nothing ->
                fail "Unbound variable"

            Just scheme -> do
                t1 <- instantiate scheme
                pure ( mempty, t1 )

    Lit (Int _) ->
        pure ( mempty, TInt )

    Lit (Bool _) ->
        pure ( mempty, TBool )

    Lam name body -> do
        t <- fresh
        let env' = extend name (Forall mempty t) context
        ( s1, t1 ) <- infer env' body
        pure ( s1, TArr (apply s1 t) t1 )

    App fun arg -> do
        t <- fresh
        ( s1, t1 ) <- infer context fun
        ( s2, t2 ) <- infer (apply1 s1 context) arg
        s3 <- unify (apply s2 t1) (TArr t2 t)
        pure ( s3 `compose` s2 `compose` s1, apply s3 t )

    Let name expr body -> do
        ( s1, t1 ) <- infer context expr
        let env' = apply1 s1 context
            t'   = generalize env' t1
        ( s2, t2 ) <- infer (extend name t' env') body
        pure ( s1 `compose` s2, t2 )

    If cond true false -> do
        ( s1, t1 ) <- infer context cond
        ( s2, t2 ) <- infer context true
        ( s3, t3 ) <- infer context false
        s4 <- unify t1 TBool
        s5 <- unify t2 t3
        pure ( s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, apply s5 t2 )

    Fix expr -> do
        ( s1, t1 ) <- infer context expr
        t <- fresh
        s2 <- unify (TArr t t) t1
        pure ( s2, apply s1 t )

    Op op a b -> do
        ( s1, t1 ) <- infer context a
        ( s2, t2 ) <- infer context b
        t <- fresh
        s3 <- unify (TArr t1 (TArr t2 t)) (ops Map.! op)
        pure ( s1 `compose` s2 `compose` s3, apply s3 t )


ops :: Map Op Type
ops = Map.fromList 
    [ ( Add, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Mul, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Sub, (TInt `TArr` (TInt `TArr` TInt)) )
    , ( Eq, (TInt `TArr` (TInt `TArr` TBool)) )
    ]


-- http://www.macs.hw.ac.uk/~yl55/UnPublished/ThesisMainText.pdf
--
unify :: Type -> Type -> Unify Sub
unify = curry $ \case 
    ( TBool, TBool ) -> 
        pure mempty

    ( TInt, TInt ) -> 
        pure mempty

    ( a `TArr` b, a1 `TArr` b1 ) -> do
        t1 <- unify a a1
        t2 <- unify (apply t1 b) (apply t1 b1)
        pure (t2 `compose` t1)

    ( TVar a, TVar b ) 
        | a == b -> pure mempty

    ( tau, TVar name ) -> 
        unify (TVar name) tau

    ( TVar name, tau ) 
        | name `occursIn` tau -> fail "Infinite type"
        | otherwise           -> pure (substitute name tau)

    _ -> 
        fail "Unification failed"

  where
    occursIn name = member name . free


apply :: Sub -> Type -> Type
apply sub = \case 
    TVar name ->
        Map.findWithDefault (TVar name) name sub

    TArr t1 t2 ->
        TArr (apply sub t1) (apply sub t2)

    tau ->
        tau


fresh :: Unify Type
fresh = do
    count <- counterStep
    let var = letters !! count
    pure (TVar var)


letters = fmap Text.pack ( [1..] >>= flip replicateM ['a'..'z'] )


runInfer :: Unify a -> a
runInfer state =
    evalState state newUniState 


-------------------------------------------------------------------------------

expr1 = Lam "x" (Op Add (Var "x") (Lit (Int 1)))

expr2 = App expr1 (Lit (Int 3))

expr3 = -- let x = 4 in let x = 5 in x
    Let "x" (Lit (Int 4)) (Let "x" (Lit (Int 5)) (Var "x"))

expr4 = 
    Let "x" (Lit (Int 4)) (Let "y" (Lit (Int 5)) (Var "x"))

fact =
    Fix (Lam "f"
        (Lam "n"
            (If (Op Eq (Lit (Int 0)) (Var "n"))
                (Lit (Int 1))
                (Op Mul (Var "n") (App (Var "f") (Op Sub (Var "n") (Lit (Int 1))))))
        )
    )

fact5 = App fact (Lit (Int 5))

expr1Type = runInfer (infer (Context mempty) expr1)

expr2Type = runInfer (infer (Context mempty) expr2)

main :: IO ()
main = do
   print (runReader (eval fact5) mempty, 120)
   print (runReader (eval expr1) mempty)
   print (runReader (eval expr2) mempty, 4)
   print (runReader (eval expr3) mempty, 5)
   print (runReader (eval expr4) mempty, 4)
   print (snd expr1Type)
   print (snd expr2Type)
