{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main where

--import Debug.Trace
--import Tau.Expr
import Control.Monad.Except
--import Control.Monad.Identity
--import Control.Monad.Reader
import Control.Monad.Supply
--import Data.Void
import Tau.Solver
import Tau.Type
--import Tau.Eval
--import Tau.Parser
import Tau.Util
--import Tau.Value
--import Text.Megaparsec hiding (ParseError)
--import Text.Megaparsec.Char

--type Parser = ParsecT Void String
--
--parseExpr2 :: Monad m => m (Either (ParseErrorBundle String Void) Int)
--parseExpr2 = runParserT undefined undefined undefined
--
----
--
--type InferTStack m a = ReaderT Int (ExceptT TypeError (SupplyT Int m)) a
--
--newtype InferT m a = InferT (InferTStack m a) 
--  deriving (Functor, Applicative, Monad, MonadReader Int, MonadSupply Int, MonadError TypeError)
--
--instance MonadTrans InferT where
--    lift = InferT . lift . lift . lift
--
--inferStuff :: Monad m => Int -> InferT m Int
--inferStuff = undefined
--
----
--
--type EvalTStack m a = ReaderT Int (ExceptT () m) a
--
--newtype EvalT m a = EvalT { unEvalT :: EvalTStack m a } 
--  deriving (Functor, Applicative, Monad, MonadReader Int, MonadError ())
--
--evalStuff :: Monad m => Int -> EvalT m Int
--evalStuff = undefined
--
--
----
--
--type MStackT a = InferT (EvalT (ParsecT Void String IO)) a

--

--xxx :: MStackT a
--xxx = do
--    a <- parseExpr2
--    b <- inferStuff 5
--    c <- lift $ evalStuff 5
--    undefined

main :: IO ()
main = pure ()

--cs1 :: [TypeConstraint]
--cs1 = 
--    [ Implicit (varT "a2") (varT "a1") (Monoset mempty)
--    , Explicit (varT "a1") (Forall ["a"] [TyCl "Num" (varT "a")] (arrT (varT "a") (arrT (varT "a") (varT "a"))))
--    ]
--
--runSolver :: IO (Either UnificationError (Substitution Type, [TyClass]))
--runSolver = evalSupplyT (runExceptT (solveTypes cs1)) (nameSupply "$$a")
