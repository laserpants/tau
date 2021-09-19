{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE LambdaCase                 #-}
-- {-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
module Main where

import Control.Arrow ((<<<))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Aeson hiding (Value)
import Data.Aeson.Encode.Pretty
import Data.Fix (Fix(..))
import Data.Function (fix)
import Data.Functor.Foldable
import Data.Maybe (fromJust)
import Data.Text (Text, pack, unpack)
import Data.Text (pack)
import Debug.Trace
import Prettyprinter
import Stuff
import System.Environment
import Tau.Env (Env(..))
import Tau.Eval
import Tau.Eval.Prim
import Tau.Misc
import Tau.Prettyprinters
import Tau.Serializers
import Tau.Util (Coalgebra, Name)
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Text as Text
import qualified Tau.Env as Env

newtype EvalX a = EvalX { unEvalX :: ReaderT (ValueEnvX EvalX) (Either Text) a } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadFix
    , MonadError Text
    , MonadReader (ValueEnvX EvalX) )

runEvalX :: EvalX a -> ValueEnvX EvalX -> Either Text a
runEvalX = runReaderT . unEvalX

evalExprX :: Core -> ValueEnvX EvalX -> Either Text (ValueX EvalX)
evalExprX = runEvalX . interpret

type ValueEnvX m = Env (m (ValueX m))

data ValueX m
    = ValueX Prim
    | DataX Name [ValueX m]
    | ClosureX Name (m (ValueX m)) (ValueEnvX m)
    | PrimFunX Name Fun [ValueX m]

instance Show (ValueX m) where
    show (ValueX prim)          = "Value "   <> "(" <> show prim <> ")"
    show (DataX name vs)        = "Data "    <> show name <> " " <> show vs
    show (PrimFunX name _ args) = "PrimFun " <> show name <> " " <> show args
    show ClosureX{}             = "<<function>>"

--interpret2 
--  :: (MonadFix m, MonadError Text m, MonadReader (ValueEnvX m) m)
--  => Core
--  -> m (ValueX m)
--interpret2 = interpret <=< fooz
--
--fooz
--  :: (MonadFix m, MonadError Text m, MonadReader (ValueEnvX m) m)
--  => Core
--  -> m Core
--fooz = cata $ \case
--
--    CVar var -> pure (cVar var)
--    CLit lit -> pure (cLit lit)
--    CApp exs -> cApp <$> sequence exs
--    CLam var e1 -> cLam var <$> e1
--
--    CLet var e1 e2 -> do
--        e <- mfix (\val -> local (Env.insert var (interpret2 val)) e1)
--        --e <- local (Env.insert var (interpret2 val)) e1)
--        cLet var e <$> e2
--
--    CIf e1 e2 e3 -> cIf <$> e1 <*> e2 <*> e3
--    CPat expr clauses -> cPat <$> expr <*> traverse sequence clauses
--
----subst :: Name -> Core -> m (ValueX m) -> m (ValueX m)
--subst name expr = undefined

interpret
  :: (MonadFix m, MonadError Text m, MonadReader (ValueEnvX m) m)
  => Core
  -> m (ValueX m)
interpret core = do
    traceShowM core
    cata alg core

  where
    alg = \case

        CVar var -> evalVarX var
        CLit lit -> pure (ValueX lit)
        CApp exs -> foldl1 evalAppX exs

        CLam var e1 ->
            asks (ClosureX var e1)

        --ClosureX Name (m (ValueX m)) (ValueEnvX m)
        CLet var e1 e2 -> do
            --e <- e1       -- (\e -> (Env.insert var undefined))
            let e = mfix (\val -> local (Env.insert var (pure val)) e1)
    --        e <- local (Env.insert var undefined) e1  -- (ClosureX undefined undefined e
            --e <- mfix (\val -> local (Env.insert var (ClosureX "_" (pure val) mempty)) (subst var (cApp [cVar var, cVar "_"]) e1))
            --local (Env.insert var e) e2

            local (Env.insert var e) e2

        CIf e1 e2 e3 ->
            e1 >>= \case
                ValueX (TBool isTrue) ->
                    if isTrue then e2 else e3

                _ ->
                    throwError "If clause: not a boolean"

        CPat expr clauses ->
            evalPatX expr clauses 

evalPatX 
  :: (MonadError Text m, MonadReader (ValueEnvX m) m) 
  => m (ValueX m) 
  -> CMatrix (m (ValueX m)) 
  -> m (ValueX m)
evalPatX val = \case

    [] -> throwError "Implementation error (evalPat)"
    [(["$_"], e)] -> e

    ((ps@[p, _, _], e):_) | isRowCon p ->
        undefined

    ((p:ps, e):eqs) ->
        val >>= \case
        
            DataX con args | p == con ->
                --local (Env.inserts (zip ps args)) e
                local (Env.inserts (zip ps (pure <$> args))) e

            _ -> do
                traceShowM "evalPatX"
                evalPatX val eqs 

--getFieldX :: (Monad m) => Name -> [Value m] -> m (Value m)
getFieldX name [DataX f (v:fs)]
    | f == ("{" <> name <> "}") = pure v
    | otherwise                 = getFieldX name fs

--closureX :: (MonadReader (ValueEnv m) m) => Name -> m (Value m) -> m (Value m)
closureX var a = pure (ClosureX var a mempty)

evalVarX 
  :: (MonadError Text m, MonadReader (ValueEnvX m) m) 
  => Name 
  -> m (ValueX m)
evalVarX var = do
    traceShowM var
    case Text.stripPrefix "@" var of

        Just "(!).getField" ->
            closureX "?a" $ do
                env <- ask
                xx1 <- fromJust (Env.lookup "?a" env)
                traceShowM xx1
                let (ValueX (TSymbol name)) = xx1
                closureX "?b" $ do
                    env <- ask
                    xx2 <- fromJust (Env.lookup "?b" env)
                    traceShowM xx2
                    let DataX "!" fields = xx2
                    --DataX "!" fields <- fromJust (Env.lookup "?b" env)
                    ----ClosureX var body _ <- getFieldX (withInitialLower_ name) fields
                    case getFieldX (withInitialLower_ name) fields of
                        Just (ClosureX var body _) -> 
                            local (Env.insert var (pure (ValueX TUnit))) body

        Just prim -> do
            case Env.lookup prim primEnv of
                Just fun ->
                    evalPrimX prim fun []

                Nothing -> do
                    throwError ("No primitive function " <> prim)

        _ -> do
            --case Env.lookup var env of
            --    Just value -> 
            --        value

            --    _ ->
            --        throwError ("Unbound identifier '" <> var <> "'")

            asks (Env.lookup var) >>= \case
                Just value -> do
                    y <- value
                    traceShowM y
                    value

                _ ->
                    if isConstructor var
                        then 
                            pure (DataX var [])

                        else
                            throwError ("Unbound identifier '" <> var <> "'")

--isConstructorX :: Name -> Bool
--isConstructorX var
--    | isUpper init = True
--  where
--    init = Text.head var

evalPrimX
  :: (MonadError Text m, MonadReader (ValueEnvX m) m)
  => Name
  -> Fun
  -> [ValueX m]
  -> m (ValueX m)
evalPrimX name fun args
    | arity fun == length args =
        ValueX . applyFun fun <$> traverse literal (reverse args)

    | otherwise =
        pure (PrimFunX name fun args)

  where
    literal (ValueX lit) = pure lit
    literal _            = throwError "Implementation error (evalPrim)"

evalAppX
  :: (MonadError Text m, MonadReader (ValueEnvX m) m)
  => m (ValueX m)
  -> m (ValueX m)
  -> m (ValueX m)
evalAppX fun arg = do
    traceShowM "evalAppX"
    
--    val <- arg
    fun >>= \case

        ClosureX var body closure ->
            --local (Env.insert var val closure <>) body
            local (Env.insert var arg closure <>) body

        PrimFunX name fun args -> do
            val <- arg
            traceShowM "evalPrimX"
            evalPrimX name fun (val:args)

--        DataX "succ" args -> do

        DataX con args -> do
            a <- arg
            pure (DataX con (args <> [a]))

-------------------------------------------------------------------------------------------------------------------

x =
  let fn = \n m -> if n == 0 then m else fn (n - 1) (m + 1)
   in fn 5 8  -- 13


--
-- let
--   fn =
--     (n, m) =>
--       if n == 0
--         then
--           m
--         else
--           fn(n - 1, m + 1)
--   in
--     fn(5, 8)
--
fff123 =
    cLet "fn"
        (cLam "n"
            (cLam "m"
                (cIf (cApp [cVar "@Int.(==)", cVar "n", cLit (TInt 0)])
                    (cVar "m")
                    (cApp [ cVar "fn"
                          , cApp [cVar "@Int.(-)", cVar "n", cLit (TInt 1)]
                          , cApp [cVar "@Int.(+)", cVar "m", cLit (TInt 1)] ]))))
        (cApp [cVar "fn", cLit (TInt 5), cLit (TInt 8)])


fff124 =
  cLet "fst"
      (cLam "$p" (cPat (cVar "$p") 
          [ (["(,)", "$f0", "$f1"], cVar "$f0")
          ]))
      (cLet "snd"
          (cLam "$p" (cPat (cVar "$p") 
              [ (["(,)", "$f0", "$f1"], cVar "$f1")
              ]))
          (cLet "unfolds" 
              (cLam "$e1"      -- f
                  (cLam "$e0"  -- n
                      (cLet "x" 
                          (cApp [cVar "$e1", cVar "$e0",   -- f(n, unfolds(f, fst(x)))
                              cApp [cVar "unfolds", cVar "$e1"], cApp [cVar "fst", cVar "x"]])
                          (cApp [cVar "snd", cVar "x"])
                          )))
              (cLet "foo"
                  (cLam "$e8"      -- n
                      (cLam "$e7"  -- next
                          (cApp 
                              [ cVar "(,)"
                              -- n + 1
                              , cApp [cVar "@Int.(+)", cVar "$e8", cLit (TInt 1)] 
                              -- ( head = () => n, tail = () => Stream(next) )
                              , cApp 
                                  [ cVar "!"
                                  , cApp 
                                      [ cVar "{head}"
                                      , cLam "_" (cVar "$e8")
                                      , cApp 
                                          [ cVar "{tail}"
                                          , cLam "_" (cApp [cVar "Stream", cVar "$e7"])
                                          , (cVar "{}")
                                          ]
                                      ]
                                  ]
                              ])))
                  (cLet "unStream"
                      (cLam "s" (cPat (cVar "s") [ (["Stream", "s"], cVar "s") ]))
                      (cLet "s"
                          -- Stream(unfolds(foo, 1))
                          (cApp [cVar "Stream", cApp [cVar "unfolds", cVar "foo", cLit (TInt 1)]])
                          -- unStream(s).Head
                          (cApp [cVar "@(!).getField", cLit (TSymbol "Head"), cApp [cVar "unStream", cVar "s"]]))
                  )
              )))

-------------------------------------------------------------------------------------------------------------------

data StreamCodata a = StreamCodata
    { _head :: () -> a
    , _tail :: () -> Stream a
    }

data Stream a = Stream (StreamCodata a)

unfolds :: ((a, b) -> (a, b)) -> a -> b
unfolds f n = let (m, s) = f (n, unfolds f m) in s

enumFroms :: Int -> Stream Int
enumFroms n =
    Stream (unfolds fun n)
  where
    fun :: (Int, StreamCodata Int) -> (Int, StreamCodata Int)
    fun (n, next) = (n + 1, StreamCodata{ _head = \_ -> n, _tail = \_ -> Stream next })

tails :: Stream a -> Stream a
tails (Stream (StreamCodata { _tail = t })) = t ()

heads :: Stream a -> a
heads (Stream (StreamCodata { _head = h })) = h ()



--data Stream = Stream
--    { _head :: Int
--    , _tail :: Stream
--    } deriving (Show, Eq)
--
--
--implFun :: (a -> s -> (a, s)) -> a -> s
--implFun f n = let (m, s) = f n (implFun f m) in s
--
--clientFun :: Int -> Stream -> (Int, Stream)
--clientFun n next = (n + 1, Stream { _head = n, _tail = next })
--
--
--go = implFun clientFun 1
--
--foo = _head go


--data StreamF a = StreamF
--    { _head :: Int
--    , _tail :: StreamF a }
--    deriving (Show, Eq, Functor)
--
--type Stream = Fix StreamF
--
---- para - apo
--
--build :: Int -> Stream
--build n = apo go n where
--  go :: Int -> StreamF (Either Stream Int)
----  go 0 = StreamF { _head = 1, _tail = StreamF { _head = 1, _tail = undefined } }
--  go n = StreamF { _head = 1, _tail = undefined }



main :: IO ()
main = do
    [p] <- getArgs


    -- (False.foo)({ foo = ... })

    -- (foo(False))({ foo = ... })

    -- (foo(False, { foo = ... })

    --let p = "{ foo = () => true }.foo(false)"
--    let p = "{ foo = () => true }.foo()"

--    let p = "{ foo = _ => \"Hello\" }.foo(0)"

--    let p = "let g = (x : int) => x + 3 in let f = (x : int) => x + 1 in 5.f.g"

--    let p = "{ foo = x => \"Hello\" }.foo(false)"

    -- B.putStrLn (encodePretty' defConfig{ confIndent = Spaces 2 } (toRep (runBundle (pack p))))
--    let p = "let f(x) = x > 3 in f(3 : int)"

--    let xx = (runBundle (pack p))
--    let ff = encode (toRep xx)
--
--    traceShowM ((coreExpr xx))
--
--    putChar (B.head ff)


    B.putStrLn (encode (toRep (runBundle (pack p))))


--let f(x) = x + 1 > 5 in f(5)

--let foo
--  | 0 => 1
--  | n => 2
--  in foo(1)


-- let
--   foo(x) =
--     x > 5
--   in
--     foo(8)
--

-- let f(x) = x + 1 in f(123)

-- let f(x) = x + 1 in f(123 : int)
--
--
-- let f(x) = 11 in x => show(read(x))
--
