{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE RecordWildCards   #-}
module Main where

import Control.Monad.Except
import Control.Monad.Extra (allM, (||^))
import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Trans.Maybe
import Data.Aeson
import Data.Aeson.Encode.Pretty
import Data.Either.Combinators (rightToMaybe, fromRight)
import Data.Foldable (foldlM, foldrM)
import Data.Function ((&))
import Data.List (nub)
import Data.Maybe
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import System.Environment 
import Tau.Compiler.Bundle
import Tau.Compiler.Error
import Tau.Compiler.Patterns
import Tau.Compiler.Pipeline.Stage0 
import Tau.Compiler.Pipeline.Stage1 
import Tau.Compiler.Pipeline.Stage2 
import Tau.Compiler.Pipeline.Stage3 
import Tau.Compiler.Pipeline.Stage4 
import Tau.Compiler.Pipeline.Stage5 
import Tau.Compiler.Pipeline.Stage6 
import Tau.Compiler.Substitute
import Tau.Compiler.Typecheck
import Tau.Compiler.Unify
import Tau.Core
import Tau.Eval
import Tau.Lang
import Tau.Parser
import Tau.Prog
import Tau.Serialize
import Tau.Type
import Tau.Util
import Text.Megaparsec
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Set.Monad as Set
import qualified Data.Text.IO as Text
import qualified Tau.Compiler.Pipeline.Stage0 as Stage0
import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
import qualified Tau.Compiler.Pipeline.Stage6 as Stage6
import qualified Tau.Env as Env
import DevTests


layoutOpts = (LayoutOptions {layoutPageWidth = AvailablePerLine 10 1.0})

renderDoc2 :: Doc a -> Text
renderDoc2 = renderStrict . layoutPretty layoutOpts

prettyPrint2 :: (Pretty p) => p -> IO ()
prettyPrint2 = Text.putStrLn . renderDoc2 . pretty

prettyDoc2 :: Doc a -> IO ()
prettyDoc2 = Text.putStrLn . renderDoc2 



epxr123 :: ProgExpr ()
epxr123 =
    letExpr () (BPat () (varPat () "x"))
        (ifExpr ()
            (op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10)))
            (patExpr () (varExpr () "x")
                    [ Clause () [ conPat () "Some" [varPat () "z"] ] 
                        [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
                        , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
                        , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
                        ]
                    , Clause () [ conPat () "Some" [varPat () "z"] ] 
                        [ Guard [] (litExpr () (TInt 2)) 
                        ]
                    , Clause () [ conPat () "None" [] ] 
                        [ Guard [] (litExpr () (TInt 3)) 
                        ]
                    ])
            (patExpr () (varExpr () "x")
                    [ Clause () [ conPat () "Some" [varPat () "z"] ] 
                        [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
                        , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
                        , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
                        ]
                    , Clause () [ conPat () "Some" [varPat () "z"] ] 
                        [ Guard [] (litExpr () (TInt 2)) 
                        ]
                    ]))
        (litExpr () (TInteger 3))


--epxr123 :: ProgExpr ()
--epxr123 =
--    letExpr () (BPat () (varPat () "x"))
--        (ifExpr ()
--            (op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10)))
--            (litExpr () (TInteger 3))
--            (patExpr () (varExpr () "x")
--                    [ Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
--                        , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
--                        , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
--                        ]
--                    , Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [] (litExpr () (TInt 2)) 
--                        ]
--                    ]))
--        (litExpr () (TInteger 3))


--epxr123 :: ProgExpr ()
--epxr123 =
--    letExpr () (BFun () "fn" [varPat () "x", varPat () "y"])
--        (ifExpr ()
--            (op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10)))
--            (litExpr () (TInteger 3))
--            (patExpr () (varExpr () "x")
--                    [ Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
--                        , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
--                        , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
--                        ]
--                    , Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [] (litExpr () (TInt 2)) 
--                        ]
--                    ]))
--        (litExpr () (TInteger 3))


--epxr123 :: ProgExpr ()
--epxr123 =
--    lamExpr () [varPat () "x", varPat () "y"]
--        (ifExpr ()
--            (op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10)))
--            (litExpr () (TInteger 3))
--            (patExpr () (varExpr () "x")
--                    [ Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
--                        , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
--                        , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
--                        ]
--                    , Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [] (litExpr () (TInt 2)) 
--                        ]
--                    ]))

--epxr123 :: ProgExpr ()
--epxr123 = 
--    ifExpr ()
--        (op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10)))
--        (litExpr () (TInteger 3))
--        (patExpr () (varExpr () "x")
--                [ Clause () ( conPat () "Some" [varPat () "z"] ) 
--                    [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
--                    , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
--                    , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
--                    ]
--                , Clause () ( conPat () "Some" [varPat () "z"] ) 
--                    [ Guard [] (litExpr () (TInt 2)) 
--                    ]
--                ])


--epxr123 :: ProgExpr ()
--epxr123 = 
--    letExpr () 
--        (BPat () (varPat () "f"))
--        (lamExpr () [varPat () "t"]
--            (patExpr () (varExpr () "t")
--                    [ Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
--                        , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
--                        , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
--                        ]
--                    , Clause () ( conPat () "Some" [varPat () "z"] ) 
--                        [ Guard [] (litExpr () (TInt 2)) 
--                        ]
--                    ]))
--        (varExpr () "x")


--epxr123 :: ProgExpr ()
--epxr123 = 
--    letExpr () (BPat () (varPat () "x"))
--        (funExpr () 
--            [ Clause () ( conPat () "Some" [litPat () (TBool True)] ) [ Guard [] (annExpr tInt (litExpr () (TInt 1))) ]
--            , Clause () ( conPat () "Some" [litPat () (TBool False)] ) [ Guard [] (litExpr () (TInt 2)) ]
--            ])
--        (varExpr () "y")

--epxr123 :: ProgExpr ()
--epxr123 = 
--    patExpr () (varExpr () "x")
--            [ Clause () ( conPat () "Some" [varPat () "z"] ) 
--                [ Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 10))] (annExpr tInt (litExpr () (TInt 1))) 
--                , Guard [op2Expr () (OGt ()) (varExpr () "z") (litExpr () (TInteger 5))] (annExpr tInt (litExpr () (TInt 2))) 
--                , Guard [] (annExpr tInt (litExpr () (TInt 3))) 
--                ]
--            , Clause () ( conPat () "Some" [varPat () "z"] ) 
--                [ Guard [] (litExpr () (TInt 2)) 
--                ]
--            ]


class Foo a where
    foo :: a -> Bool

instance Foo Int where
    foo _ = True

test001 :: Int
test001 =
  let fn = \x -> 
            case x of
                Just a -> if foo a then 1 else 2
                Nothing -> 3 :: Int
  in 
    --fn Nothing
    --fn Nothing 
    fn (Just (1 :: Int))


-----------------------
-----------------------

--super :: ClassEnv -> Name -> [Name]
--super env name =
--    maybe [] (fmap predicateName . classPredicates . fst) (Env.lookup name env)
--
--type Instance = ClassInfo Type (Ast (TypeInfo ()))

--instances :: ClassEnv -> Name -> [Instance]
--instances env name = fromMaybe [] (snd <$> Env.lookup name env)
--
--bySuper :: ClassEnv -> Predicate -> [Predicate]
--bySuper env self@(InClass name ty) =
--    self:concat [bySuper env (InClass tc ty) | tc <- super env name]

--byInstance :: (MonadSupply Name m) => ClassEnv -> Predicate -> m (Maybe [Predicate])
--byInstance env self@(InClass name ty) = do
--    msum <$> (rightToMaybe <$$> sequence [runExceptT (tryInstance i) | i <- instances env name])
--  where
--    tryInstance :: (MonadSupply Name m) => Instance -> ExceptT UnificationError m [Predicate]
--    tryInstance ClassInfo{..} =
--        applyBoth <$> matchClass classSignature self 
--                  <*> pure classPredicates
--
--entail :: (MonadSupply Name m) => ClassEnv -> [Predicate] -> Predicate -> m (Either a Bool)
--entail env cls0 cl = do -- pure super ||^ instances
--    x <- instances
--    pure (pure super ||^ x)
--  where
--    super :: Bool
--    super = any (cl `elem`) (bySuper env <$> cls0)
--    instances :: (MonadSupply Name m) => m (Either a Bool)
--    instances = do
--        zz <- byInstance env cl
--        case zz of
--            Nothing   -> pure (Right False)
--            Just cls1 -> do
--                x <- mapM (entail env cls0) cls1
--                let zzz = all too x 
--                pure (Right zzz)
--
--    too a = case a of
--        Right True -> True
--        _          -> False
--
----        undefined
----        case zz of
----            Nothing   -> pure (Right False)
----            Just cls1 -> do
----                xx <- entail env cls0
----                undefined -- allM (entail env cls0) cls1
--
----    instances = case byInstance env cl of
----        Nothing   -> pure False
----        Just cls1 -> allM (entail env cls0) cls1
--
----isHeadNormalForm :: Predicate -> Bool
----isHeadNormalForm (InClass _ t) = 
----    flip cata t $ \case
----        TApp _ t1 _ -> t1
----        TVar{}      -> True
----        _           -> False
--
--toHeadNormalForm :: (MonadSupply Name m) => ClassEnv -> [Predicate] -> m (Either a [Predicate])
--toHeadNormalForm env ps = do
--    z <- mapM (hnf env) ps
--    pure (Right (concat (concat (sequence z))))
--  where
----  hnf :: ClassEnv -> Predicate -> m (Either a [Predicate])
--    hnf env tycl 
--        | isHeadNormalForm tycl = pure (Right [tycl])
--        | otherwise = byInstance env tycl >>= \case
--            Nothing  -> pure (Left ContextReductionFailed)
--            Just cls -> toHeadNormalForm env cls
--
--simplify :: (MonadSupply Name m) => ClassEnv -> [Predicate] -> m (Either a [Predicate])
--simplify env = loop [] 
--  where
--    loop :: (MonadSupply Name m) => [Predicate] -> [Predicate] -> m (Either a [Predicate])
--    loop qs [] = pure (Right qs)
--    loop qs (p:ps) = entail env (qs <> ps) p >>= \case
--        Left  e -> pure (Left e)
--        Right b -> if b then loop qs ps else loop (p:qs) ps
--
--
--reduce :: (MonadSupply Name m) => ClassEnv -> [Predicate] -> m (Either a [Predicate])
--reduce env cls = join <$> (toHeadNormalForm env cls >>= traverse (simplify env))


--unifyClass, matchClass 
--  :: (MonadSupply Name m, MonadError UnificationError m) 
--  => Predicate 
--  -> Predicate 
--  -> m (Substitution Type, Substitution Kind)
--unifyClass = liftU unifyTypes
--matchClass = liftU matchTypes
--
--liftU 
--  :: (MonadSupply Name m, MonadError UnificationError m) 
--  => (Type -> Type -> m a) 
--  -> Predicate 
--  -> Predicate 
--  -> m a
--liftU m (InClass c1 t1) (InClass c2 t2)
--    | c1 == c2  = m t1 t2
--    | otherwise = throwError ClassMismatch



-----------------------
-----------------------

insertDicts 
  :: (MonadSupply Name m)
  => Context
  -> ConstructorEnv
  -> ClassEnv
  -> Ast (TypeInfo [e])
  -> m (Ast (TypeInfo [e]))
insertDicts env constructorEnv classEnv ast = 
    pure ast


--  TODO
--  TODO
--  TODO
--    forM ast (\TypeInfo{..} -> do
--        ps <- fromRight undefined <$> reduce classEnv (predicates nodeType <> nodePredicates)
--        pure $ TypeInfo { nodePredicates = ps, .. })
--  TODO
--  TODO
--  TODO


  where
--    foo :: (MonadSupply Name m) => Type -> [Predicate] -> m [Predicate]
--    foo t ps = do
--        fromRight undefined <$> reduce classEnv (predicates <> ps) --  >>= \case
----            Left e -> undefined
----            Right r -> pure r
--      where
--        predicates :: [Predicate]
        predicates t = do
            var <- (fst <$> free t)
            set <- maybeToList (Env.lookup var env)
            name <- Set.toList set
            pure (InClass name (tVar kTyp var))

--    zzz2 ast
--    --pure (fmap zzz ast)
--  where
----    xx = traverse zzz ast
--
--    zzz2 :: Monad m => Ast (TypeInfo [e]) -> m (Ast (TypeInfo [e]))
--    zzz2 a = do
--        let -- xx :: Ast (m (TypeInfo [e]))
--            xx = fmap zzz a
--        sequence xx
--
--    zzz :: Monad m => TypeInfo [e] -> m (TypeInfo [e])
--    zzz TypeInfo{..} = 
--        pure $ TypeInfo{ nodePredicates = predicates nodeType <> nodePredicates, .. }
--
--    predicates :: Type -> [Predicate]
--    predicates t = [InClass name (tVar kTyp t) | (t, set) <- vars, name <- Set.toList set]
--      where
--        vars = [(var, cls) | var <- (fst <$> free t), cls <- maybeToList (Env.lookup var env)]


    --moo :: (MonadSupply Name m) => Ast (TypeInfo [e]) -> m (Ast (TypeInfo [e]))
    --moo ast = Ast <$> cata alg (astExpr ast) 
    --  where
    --    alg = \case
    --        EVar    t var        -> varExpr   <$> boo t <*> pure var
    --        ECon    t con es     -> conExpr   <$> boo t <*> pure con <*> sequence es
    --        ELit    t prim       -> litExpr   <$> boo t <*> pure prim
    --        EApp    t es         -> appExpr   <$> boo t <*> sequence es
    --        ELet    t bind e1 e2 -> letExpr   <$> boo t <*> binding bind <*> e1 <*> e2
    --        EFix    t name e1 e2 -> fixExpr   <$> boo t <*> pure name <*> e1 <*> e2
    --        ELam    t ps e       -> lamExpr   <$> boo t <*> traverse pattern ps <*> e
    --        EIf     t e1 e2 e3   -> ifExpr    <$> boo t <*> e1 <*> e2 <*> e3 
    --        EPat    t e cs       -> patExpr   <$> boo t <*> e <*> traverse clause cs
    --        EFun    t cs         -> funExpr   <$> boo t <*> traverse clause cs
    --        EOp1    t op a       -> op1Expr   <$> boo t <*> pure op <*> a
    --        EOp2    t op a b     -> op2Expr   <$> boo t <*> pure op <*> a <*> b
    --        ETuple  t es         -> tupleExpr <$> boo t <*> sequence es
    --        EList   t es         -> listExpr  <$> boo t <*> sequence es
    --        ERow    t lab a b    -> rowExpr   <$> boo t <*> pure lab <*> a <*> b
    --        EAnn    _ e          -> e

    --    binding = \case
    --        BPat    t p          -> BPat      <$> boo t <*> pattern p
    --        BFun    t name ps    -> BFun      <$> boo t <*> pure name <*> traverse pattern ps

    --    clause = \case
    --        Clause  t p gs       -> Clause    <$> boo t <*> pattern p <*> traverse guard gs

    --    guard = \case
    --        Guard es e           -> Guard     <$> sequence es <*> e

    --    pattern = cata $ \case
    --        PVar    t var        -> varPat    <$> boo t <*> pure var
    --        PCon    t con ps     -> conPat    <$> boo t <*> pure con <*> sequence ps
    --        PLit    t prim       -> litPat    <$> boo t <*> pure prim
    --        PAs     t as p       -> asPat     <$> boo t <*> pure as <*> p
    --        POr     t p q        -> orPat     <$> boo t <*> p <*> q
    --        PAny    t            -> anyPat    <$> boo t
    --        PTuple  t ps         -> tuplePat  <$> boo t <*> sequence ps
    --        PList   t ps         -> listPat   <$> boo t <*> sequence ps
    --        PRow    t lab p q    -> rowPat    <$> boo t <*> pure lab <*> p <*> q
    --        PAnn    _ p          -> p
  
    --boo :: (MonadSupply Name m) => TypeInfo [e] -> m (TypeInfo [e])
    --boo TypeInfo{..} = do
    --    ps <- foo nodeType nodePredicates
    --    pure $ TypeInfo { nodePredicates = ps, .. }

--        predicates = do
--            (t1, set) <- vars
--            name <- Set.toList set
--            pure (InClass name (tVar kTyp t1))
--
--        vars = do
--            var <- (fst <$> free t)
--            cls <- maybeToList (Env.lookup var env)
--            pure (var, cls)

--insertDicts env = fmap (\TypeInfo{..} -> 
--    TypeInfo{ nodePredicates = predicates nodeType <> nodePredicates, .. })
--  where
--    predicates :: Type -> [Predicate]
--    predicates t = [InClass name (tVar kTyp t) | (t, set) <- vars, name <- Set.toList set]
--      where
--        vars = [(var, cls) | var <- (fst <$> free t), cls <- maybeToList (Env.lookup var env)]


--insertDicts env = mapTags $ \info@NodeInfo{..} -> 
--        info{ nodePredicates = nub (nodePredicates <> predicates nodeType) }
--  where
--    predicates :: Type -> [Predicate]
--    predicates t = concat [ concat $ maybeToList (Env.lookup v env) | v <- Set.toList (free t) ]



-- Modules
--   - add module
--
-- Definitions
--   - add def
--   - add type decl.
--   - add class
--   - add instance

--data Module = Module 
--    { moduleName      :: String 
--    , moduleDefs      :: [Definition]
--    , moduleTypeDecls :: [Datatype]
--    , moduleClassEnv  :: 
--    }
--
--data Definition = Definition 
--    { defName :: String 
--    }


insertDefinition
  :: ( MonadSupply Name m
     , MonadState (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m ) 
  => Name
  -> ProgExpr () 
  -> m ()
insertDefinition name expr = do
    (classEnv, typeEnv, kindEnv, constructorEnv) <- get
    x <- runInferT mempty classEnv typeEnv kindEnv constructorEnv $ do
        Ast e <- inferAstType (Ast expr)
        undefined

    pure ()



--leaf n = Branch TNil n TNil
--
--testTree = Branch (Branch (leaf 2) 3 (Branch (leaf 4) 1 (Branch (leaf 8) 7 TNil))) 5 (Branch (leaf 2) 6 (leaf 8))
--                
--               5
--             /   \
--            3     6
--           / \   / \
--          2   1 2   8      5 + 3 + 6 + 2 + 1 + 2 + 8 + 4 + 7 + 8  = 46
--             / \
--            4   7
--               / 
--              8
--

data Tree a = Leaf | Node a (Tree a) (Tree a) deriving (Show)

data Tree' a b = Leaf' | Node' a (Tree a) (Tree a) b b deriving (Show)

testTree = Node 5 (Node 3 (Node 2 Leaf Leaf) (Node 1 (Node 4 Leaf Leaf) (Node 7 (Node 8 Leaf Leaf) Leaf))) (Node 6 (Node 2 Leaf Leaf) (Node 8 Leaf Leaf))

loopTree g (Node n t1 t2) = g (Node' n t1 t2 (loopTree g t1) (loopTree g t2))
loopTree g Leaf           = g Leaf'

height' = loopTree go testTree
  where
    go (Node' n t1 t2 a b) = 1 + max a b
    go _                   = 0


--data Tree a = TNil | Branch (Tree a) a (Tree a) deriving (Show)
--
--data TreeX a b = TNilX | BranchX (Tree a, b) a (Tree a, b) deriving (Show)
--
--fnyy g (Branch t1 n t2) = g (BranchX (t1, fnyy g t1) n (t2, fnyy g t2))
--fnyy g b                = g TNilX 
--
--heightX = fnyy g1 testTree
--  where
--    g1 (BranchX (t1, x) n (t2, y)) = 1 + max x y
--    g1 _                           = 0
--
----height 
----  | .Branch(t1, n, t2, a, b) => 1 + max a b
----  | .TNil                    => 0
--
--
--
----fny g a b1@(Branch t1 m t2) b2@(Branch t3 n t4) = fny g (g b1 b2 a) undefined
--
--fny g b@(Branch t1 _ t2) = g b [fny g t1, fny g t2]
--fny g b                  = g b []
--
--height = fny g1 testTree
--  where
--    g1 (Branch t1 n t2) [x, y] = 1 + max x y
--    g1 _                []     = 0
--
---- testTree.recurse(g1)
----
--sum_ = fny g1 testTree
--  where
--    g1 (Branch t1 n t2) [x, y] = n + x + y
--    g1 _                []     = 0
--
--
--
--
--
--data Nat = Zero | Succ Nat deriving (Show)
--
--fnx g a (Succ n) = fnx g (g (Succ n) a) n
--fnx _ a _        = a
--
--len = fnx (\_ x -> x + 1) 0 (Succ (Succ (Succ Zero)))
--
---- let f(x : Int) = x + 1 in f(127)
--
--
--
----Clause t (ProgPattern t) (ProgExpr t)

main :: IO ()
main = do
    [a] <- getArgs
    case doParse (pack a) of
        Right expr -> foo1 expr
        Left err   -> traceShowM err
    pure ()

  where
    doParse inp = runParserStack exprParser "" inp
-- -- print "Main"


--test349 = evalSupply (runReaderT (evalStateT e []) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)) (numSupply "")
--  where
--    e = (foldrM applyDicts (varExpr (Just tInt) "fn") [InClass "Eq" tInt, InClass "Num" tInt])


--test340 :: [[ProgPattern ()]]
--test340 = foo [ [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] ]

test345 = 
    evalSupply (reduce testClassEnv 
        [ InClass "Num" (tVar kTyp "a") 
        , InClass "Num" (tVar kTyp "a")
        , InClass "Foo" (tVar kTyp "a")
        ]) (numSupply "a")


test344 = tApp (kVar "k3") (tVar (kVar "k4") "m") (tVar (kVar "k5") "a")


test343 = tApp (kVar "k1") (tVar (kVar "k2") "f") (tApp (kVar "k3") (tVar (kVar "k4") "m") (tVar (kVar "k5") "a" `tArr` tApp (kVar "k6") (tCon (kVar "k7") "List") (tVar (kVar "k8") "b")))


test342 = tApp (kVar "k1") (tVar (kVar "k2") "f") (tApp (kVar "k3") (tVar (kVar "k4") "m") (tVar (kVar "k5") "a" `tArr` tVar (kVar "k6") "b"))


test341 = tApp (kVar "k1") (tVar (kVar "k2") "f") (tApp (kVar "k3") (tVar (kVar "k4") "m") (tVar (kVar "k5") "a"))

test340 = tApp (kVar "k1") (tApp (kVar "k2") (tVar (kVar "k3") "f") (tVar (kVar "k4") "m")) (tVar (kVar "k5") "a")


test339 :: ProgExpr ()
test339 = 
    letExpr ()
        (BPat () (varPat () "f"))
        (lamExpr () [annPat tInt (varPat () "x")] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))
        (appExpr () [varExpr () "f", litExpr () (TInt 123)])
        


--test338 :: ClassInfo Type (Ast (TypeInfo ()))
test338 = do  --(classSignature, classPredicates, classMethods)
    case xx of
        Right y -> mapM_ print y
  where
    exp = lookupAllClassMethods "Num" tInt testClassEnv
    --xx :: [(Name, Ast (TypeInfo ()))]
    xx = fromJust (runExceptT (evalSupplyT exp (numSupply "a")))


test337 :: IO Bool
test337 = runReaderT (exhaustive
            [ [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool False)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            , [rowPat () "x" (litPat () (TBool True)) (rowPat () "y" (recordPat () (rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))) (conPat () "{}" []))] 
            ]

    )
    testConstructorEnv 

test335 = runReader (exhaustive 
            [ [rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))] 
            , [rowPat () "z" (litPat () (TBool True)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" []))] 
            ]
    )
    testConstructorEnv 


test334b = runReader (useful
            [ [rowPat () "y" (rowPat () "z" (conPat () "#False" []) (rowPat () "a" (conPat () "#False" []) (conPat () "{}" []))) (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#False" []) (rowPat () "a" (conPat () "#True" []) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#True" [])  (rowPat () "a" (conPat () "#False" []) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#True" [])  (rowPat () "a" (conPat () "#True" []) (conPat () "{}" [])))   (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#False" []) (rowPat () "a" (conPat () "#False" []) (conPat () "{}" []))) (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#False" []) (rowPat () "a" (conPat () "#True" []) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#True" [])  (rowPat () "a" (conPat () "#False" []) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (conPat () "#True" [])  (rowPat () "a" (conPat () "#True" []) (conPat () "{}" [])))   (conPat () "{}" [])] 
            ]
      [anyPat ()]
    )
    testConstructorEnv 


--test336 :: IO Bool
--test336 = runReaderT (useful1 (xx1 <$$> 
--    [ [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))) (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))  (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))  (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))   (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))) (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))  (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))  (conPat () "{}" [])] 
--    , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))   (conPat () "{}" [])] 
--    ]) [anyPat ()])
--    testConstructorEnv 


test334 :: IO Bool
test334 = runReaderT (useful
            [ [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))) (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))   (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" []))) (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool False)) (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool False)) (conPat () "{}" [])))  (conPat () "{}" [])] 
            , [rowPat () "y" (rowPat () "z" (litPat () (TBool True))  (rowPat () "a" (litPat () (TBool True)) (conPat () "{}" [])))   (conPat () "{}" [])] 
            ]
      [anyPat ()]
    )
    testConstructorEnv 


test333 :: IO Bool
test333 = runReaderT (useful
      [ [conPat () "#False" [], conPat () "#False" []]
      , [conPat () "#False" [], conPat () "#True" []]
      , [conPat () "#True" [], conPat () "#False" []]
      ]
      [anyPat (), anyPat ()]
    )
    testConstructorEnv 




test332 :: IO Bool
test332 = runReaderT (useful
      [ [litPat () (TBool False), litPat () (TBool False)]
      , [litPat () (TBool False), litPat () (TBool True)]
      , [litPat () (TBool True), litPat () (TBool False)]
      ]
      [anyPat (), anyPat ()]
    )
    testConstructorEnv 


test331 = runReader (exhaustive 
      [ [litPat () (TBool False), litPat () (TBool False)]
      , [litPat () (TBool False), litPat () (TBool True)]
      , [litPat () (TBool True), litPat () (TBool False)]
      ]
    )
    testConstructorEnv 

test31 = runReader (exhaustive 
    [ [] :: [ProgPattern ()]
    ]) 
    testConstructorEnv 

test32 = runReader (exhaustive 
    [ [litPat () (TBool True)]
    , [litPat () (TBool False)] 
    ]) 
    testConstructorEnv 

-- False
test33 = runReader (exhaustive 
    [ [litPat () (TBool True)]
    ]) 
    testConstructorEnv 

test34 = runReader (exhaustive 
    [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
    , [conPat () "[]" []]
    , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
    ]) 
    testConstructorEnv 

test35 = runReader (exhaustive 
    [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
    , [conPat () "[]" []]
    , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
    ])
    testConstructorEnv 

test35b = runReader (clausesAreExhaustive
    [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] []
    , Clause () [conPat () "[]" []] []
    , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] []
    ])
    testConstructorEnv 

test35c = runReader (checkExhaustive (
    patExpr () (varExpr () "x")
        [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] []
        , Clause () [conPat () "[]" []] []
        , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] []
        ]))
    testConstructorEnv 

-- False
test36 = runReader (exhaustive 
    [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
    , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
    ])
    testConstructorEnv 

-- False
test36b = runReader (clausesAreExhaustive
    [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] []
    , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] []
    ])
    testConstructorEnv 

-- False
test37 = runReader (exhaustive 
    [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
    , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
    , [conPat () "(::)" [anyPat (), anyPat ()]]
    ])
    testConstructorEnv 

test38 = runReader (exhaustive 
    [ [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]]
    , [conPat () "(::)" [varPat () "z", varPat () "zs"]]
    , [conPat () "(::)" [anyPat (), anyPat ()]]
    , [conPat () "[]" []]
    ])
    testConstructorEnv 


--     -- Clauses
-- 
--     describe "\nClauses\n" $ do
-- 
--         testExhaustive
--             ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [Guard [] (litExpr () (TBool True))]
--               , Clause [varPat () "a"] [Guard [] (litExpr () (TBool False))]
--               ] :: [PatternClause] )
-- 
--         testNonExhaustive
--             ( [ Clause [conPat () "(::)" [anyPat (), anyPat ()]] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testNonExhaustive
--             ( [ Clause [varPat () "x"] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testExhaustive
--             ( [ Clause [varPat () "x"] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
--               , Clause [varPat () "x"] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testExhaustive
--             ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
--               , Clause [litPat () (TString "y")] [Guard [] (litExpr () (TBool True))]
--               , Clause [anyPat ()] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testNonExhaustive
--             ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
--               , Clause [litPat () (TString "y")] [Guard [] (litExpr () (TBool True))]
--               , Clause [anyPat ()] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testExhaustive
--             ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
--               , Clause [litPat () (TString "y")] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
--               , Clause [anyPat ()] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testExhaustive
--             ( [ Clause [litPat () (TString "x")] [Guard [] (litExpr () (TBool True))]
--               , Clause [anyPat ()] [Guard [varExpr () "pIsTrue"] (litExpr () (TBool True))]
--               , Clause [varPat () "x"] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testExhaustive
--             ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
--               , Clause [conPat () "Nil" []] [Guard [] (litExpr () (TBool True))]
--               , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testNonExhaustive
--             ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
--               , Clause [conPat () "Nil" []] [Guard [varExpr () "aEqualsB"] (litExpr () (TBool True))]
--               , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         testExhaustive
--             ( [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
--               , Clause [conPat () "Nil" []] [Guard [varExpr () "aEqualsB"] (litExpr () (TBool True))]
--               , Clause [conPat () "Nil" []] [Guard [] (litExpr () (TBool True))]
--               , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
--               ] :: [PatternClause] )
-- 
--         --
--         --    | (x :: xs)
--         --      when x > 3 => 0
--         --      when x < 3 => 1
--         --      otherwise  => 2
--         --      
--         testNonExhaustive
--             ( [ Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
--                   [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
--                   , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
--                   , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
--                   ]
--               ] :: [PatternClause] )
-- 
--         --
--         --    | x
--         --      when x > 3 => 0
--         --      when x < 3 => 1
--         --      otherwise  => 2
--         --      
--         testExhaustive
--             ( [ Clause [varPat () "x"] 
--                   [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
--                   , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
--                   , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
--                   ]
--               ] :: [PatternClause] )
-- 
--         --
--         --    | (x :: xs)
--         --      when x > 3 => 0
--         --      when x < 3 => 1
--         --      otherwise  => 2
--         --    | []         => 5
--         --      
--         testExhaustive
--             ( [ Clause [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
--                   [ Guard [op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 0)) 
--                   , Guard [op2Expr () (OLt ()) (varExpr () "x") (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
--                   , Guard [litExpr () (TBool True)] (litExpr () (TInt 2)) 
--                   ]
--               , Clause [conPat () "[]" []] [Guard [] (litExpr () (TInt 5))]
--               ] :: [PatternClause] )
-- 
--     -- Expressions
-- 
--     describe "\nExpressions\n" $ do
-- 
--         testExhaustive 
--             (letExpr () (BPat (varPat () "y")) (litExpr () (TInt 5)) (varExpr () "z") :: ProgExpr)
-- 
--         testExhaustive 
--             (letExpr () (BPat (conPat () "Id" [varPat () "y"])) (conExpr () "Id" [litExpr () (TInt 5)]) (varExpr () "y") :: ProgExpr)
-- 
--         testExhaustive 
--             (letExpr () (BPat (tupPat () [varPat () "x", varPat () "y"])) (tupExpr () [litExpr () (TInt 1), litExpr () (TInt 2)]) (varExpr () "y") :: ProgExpr)
-- 
--         testNonExhaustive 
--             (letExpr () (BPat (tupPat () [varPat () "x", litPat () (TInt 3)])) (tupExpr () [litExpr () (TInt 1), litExpr () (TInt 2)]) (varExpr () "y") :: ProgExpr)
-- 
--         testNonExhaustive 
--             (letExpr () (BPat (conPat () "Some" [varPat () "y"])) (conExpr () "Some" [litExpr () (TInt 5)]) (varExpr () "y") :: ProgExpr)
-- 
--         testNonExhaustive 
--             (lamExpr () [conPat () "Some" [varPat () "y"]] (varExpr () "y") :: ProgExpr)
-- 
--         testExhaustive 
--             (lamExpr () [conPat () "Id" [varPat () "y"]] (varExpr () "y") :: ProgExpr)
-- 
--         testNonExhaustive
--             (lamExpr () [conPat () "Id" [varPat () "x", varPat () "y"]] (
--                 patExpr () [varExpr () "x", varExpr () "y"] 
--                     [ Clause [conPat () "Cons" [varPat () "x", conPat () "Cons" [varPat () "y", varPat () "ys"]]] [Guard [] (litExpr () (TBool True))]
--                     , Clause [conPat () "Nil" []] [Guard [varExpr () "aEqualsB"] (litExpr () (TBool True))]
--                     , Clause [conPat () "Cons" [varPat () "z", conPat () "Nil" []]] [Guard [] (litExpr () (TBool True))]
--                     ]) :: ProgExpr)
-- 
-- 
-- 



test2 :: ProgExpr ()
test2 = patExpr () (litExpr () (TInt 4)) 
           [ Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]
           , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
           ]

removeNonVarPredicates :: TypeInfo e -> TypeInfo e
removeNonVarPredicates (TypeInfo e ty ps) = TypeInfo e ty (filter keep ps)
  where
    keep (InClass _ (Fix TVar{})) = True
    keep _                        = False


foo1 expr = do
    void $ runInferT mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv $ do


        --traceShowM (insertDicts ctx (Ast e))

        ast@(Ast e) <- inferAstType (Ast expr)

        --x <- inferAstType (Ast expr)

        --let r = toRep (astExpr (removeNonVarPredicates <$> Ast e))
        let r = toRep e
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData22.json" (encode r)


        (_,_,ctx) <- get
        ce <- askConstructorEnv
        le <- askClassEnv
        (Ast f) <- insertDicts ctx ce le ast
        let frees = nub $ foldr (<>) [] (free <$> Ast f)
        traceShowM frees

        let sub1 = normalizer frees
        let (Ast ggg) = fmap (apply sub1) (Ast f)


        --let ddd = eee :: [(Name, Kind)]
        --let ddd = foldr (<>) [] zzz
--        let d = zzz :: Int

        let r = toRep ggg
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData220.json" (encode r)



--        traceShowM (pretty ((insertDicts ctx (Ast e))))
--        traceShowM s

        --

        --let Ast e0 = fmap (fmap Just) (Ast e)

        let e0_1 :: ProgExpr (TypeInfoT [Error] (Type))
            e0_1 = Stage0.runExhaustivePatternsCheck testConstructorEnv e 

        --e0_1 <- withReaderT getConstructorEnv (Stage0.exhaustivePatternsCheck e0)

        --

        let Ast e0_11 = fmap (fmap Just) (Ast e0_1)

        let e1 :: Stage1.TargetExpr (TypeInfoT [Error] (Maybe Type))
            e1 = Stage1.translate e0_11
        
        let r1 = toRep e1
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData23.json" (encode r1)

        --

        let e2_1 = Stage2.translate e1

        let e2 :: Stage2.WorkingExpr (Maybe Type)
            e2 = Stage2.runTranslate testClassEnv testTypeEnv testKindEnv testConstructorEnv e2_1

--        e2 <- Stage2.translate e1

        let r2 = toRep e2
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData24.json" (encode r2)

--        traceShowM e2
--        traceShowM (pretty ggg)

        --

        let e3_1 = Stage3.translate e2

        let e3 :: Stage3.TargetExpr (Maybe Type)
            e3 = Stage3.runTranslate e3_1

--        e3 <- Stage3.translate e2

        let r3 = toRep e3
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData25.json" (encode r3)

--        traceShowM e3

        --

        let e4 = Stage4.translate e3

        let r4 = toRep e4
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData26.json" (encode r4)

--        traceShowM e4

        --

        let e5_1 = Stage5.translate e4

        let e5 = Stage5.runTranslate e5_1

--        e5 <- Stage5.translate e4

        let r5 = toRep e5
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData27.json" (encode r5)

--        traceShowM e5

        --

        e6 <- Stage6.translate e5

        let r6 = toRep e6
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData28.json" (encode r6)

--        traceShowM e6

        --

        let e7 = evalExpr e6 testEvalEnv

        let r7 = toRep e7
        liftIO $ LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData29.json" (encode r7)

        traceShowM e7

        --

        pure e


example1 :: IO () -- (ProgExpr (TypeInfo [Error]), Substitution Type, Substitution Kind, Context)
example1 = do -- foo1 expr
    traceShowM (pretty expr)
    bundle <- runReaderT (compileBundle expr) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv) 

    let value  = join (evalExpr <$> (coreExpr bundle) <*> Just testEvalEnv)
    let value2 = join (evalExpr <$> (stageX6Expr bundle) <*> Just testEvalEnv)

    traceShowM value
    traceShowM value2

    liftIO $ LBS.writeFile "/home/laserpants/code/tau-tooling/src/tmp/bundle.json" (encodePretty' defConfig{ confIndent = Spaces 2 } 
                (toRep (bundle{ value = value, value2 = value2 })))

--    traceShowM value

    pure ()
  where
    expr :: ProgExpr ()
    --expr = varExpr () "x"
    --expr = conExpr () "Some" [varExpr () "x"]
    --expr = litExpr () (TInt 5)
    --expr = letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")

    ---- let fn(r) = { a = 1 | r } in fn({ b = 2 })
    --expr = 
    --    letExpr () 
    --        (BFun () "fn" [varPat () "r"]) 
    --        (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (appExpr () [varExpr () "_#", varExpr () "r"])))
    --        (appExpr () [varExpr () "fn", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])

    --expr = letExpr () 
    --            (BPat () (varPat () "b")) 
    --            (recordExpr () (rowExpr () "x" (litExpr () (TBool True)) (conExpr () "{}" [])))
    --            (recordExpr () (rowExpr () "a" (litExpr () (TBool True)) (appExpr () [varExpr () "_#", varExpr () "b"])))

    --expr = letExpr () (BPat () (varPat () "x")) (varExpr () "id") (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TString "foo")], appExpr () [varExpr () "id", litExpr () (TInt 1)]])

--    expr = letExpr () (BPat () (varPat () "x")) (litExpr () (TBool True))
--        (letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "y"] (varExpr () "y"))
--            (op2Expr () (ODot ()) (varExpr () "f") (varExpr () "x")))

--    expr = letExpr () (BPat () (varPat () "x")) (litExpr () (TBool True))
--        (letExpr () (BFun () "f" [varPat () "y"]) (varExpr () "y")
--            (op2Expr () (ODot ()) (varExpr () "f") (varExpr () "x")))

--    expr = letExpr () (BPat () (varPat () "getA")) (funExpr () [
--            Clause () (conPat () "#" [varPat () "x"]) [Guard [] (patExpr () (varExpr () "x") [
--                Clause () (rowPat () "b" (varPat () "x") (anyPat ())) [Guard [] (varExpr () "x")]
--            ])]
--        ])
--            (letExpr () (BPat () (varPat () "r")) 
--                (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) 
--                    (appExpr () [varExpr () "getA", varExpr () "r"]))

-------------------------

--    expr =
--        letExpr ()
--            (BFun () "f" [annPat tInt (varPat () "x")])
--            (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
--            (appExpr () [varExpr () "f", litExpr () (TInt 123)])

--        letExpr ()
--            (BPat () (varPat () "f"))
--            (lamExpr () [annPat tInt (varPat () "x")] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))))
--            (appExpr () [varExpr () "f", litExpr () (TInt 123)])
--            


--    expr =
--        op2Expr () (OAdd ()) (litExpr () (TInt 1)) (litExpr () (TInt 1))

--    expr =
--        appExpr () [varExpr () "fn1", litExpr () (TInteger 1), litExpr () (TInteger 1)]

--    expr =
--        appExpr () [varExpr () "fn1", annExpr tInteger (litExpr () (TInteger 1)), litExpr () (TInteger 1)]

--    expr =
--        letExpr () 
--            (BPat () (varPat () "f"))
--            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))))
----            (varExpr () "f")
--            (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))])


--    expr =
--        appExpr () 
--          [ (funExpr () 
--                [ Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]] [ Guard [] (annExpr tInt (litExpr () (TInt 1))) ]
--                , Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]] [ Guard [] (litExpr () (TInt 2)) ]
--                , Clause () [anyPat (), anyPat ()] [ Guard [] (litExpr () (TInt 3)) ]
--                ])
--          , litExpr () (TBool True)
--          , conExpr () "Some" [litExpr () (TBool False)] ]


--    expr =
--        patExpr () 
--          (tupleExpr () [litExpr () (TBool True), conExpr () "Some" [litExpr () (TBool False)]])
--                [ Clause () [tuplePat () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]]] [ Guard [] (annExpr tInt (litExpr () (TInt 1))) ]
--                , Clause () [tuplePat () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]]] [ Guard [] (litExpr () (TInt 2)) ]
--                , Clause () [tuplePat () [anyPat (), anyPat ()]] [ Guard [] (litExpr () (TInt 3)) ]
--                ]


--    expr =
--        letExpr () 
--            (BFun () "f" [annPat tInt (varPat () "x")])
--            (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) 
----            (varExpr () "f")
--            (appExpr () [varExpr () "f", litExpr () (TInt 123)])



--    expr =
--        letExpr () 
--            (BFun () "f" [varPat () "x"])
--            (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) 
----            (varExpr () "f")
--            (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))])
--

--    expr =
--        (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) )


--    expr =
--        (letExpr () (BPat () (varPat () "a")) (lamExpr () [anyPat ()] (litExpr () (TBool True))) (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "x" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) ))


--    expr =
--        (annExpr tInt (appExpr () [varExpr () "fromInteger", litExpr () (TInteger 11)]))

--    expr =
--        (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) 



--    expr = (annExpr tInt (litExpr () (TInt 6)))

--    expr = (litExpr () (TInt 6))


--    expr = (appExpr () [varExpr () "fromInteger", litExpr () (TInteger 1)])

--    expr =
--            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))))


    -- *************************************

--    expr =
--        letExpr () 
--            (BPat () (varPat () "f"))
--            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))))
--            (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))])


--    -- *************************************
--
--    expr =
--        letExpr () 
--            (BFun () "f" [varPat () "x"])
--            (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) 
--            (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))])
--
--    -- *************************************




--    expr = 
--            letExpr () (BPat () (varPat () "r")) 
--                (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) 
--                    (op2Expr () (ODot ()) (varExpr () "b") (varExpr () "r"))
--


--    -- (let r = { a = 1, b = 2 } in ({ a = a | z }) => a)({ a = 5 ))
--
--    expr = 
--            appExpr () 
--                [ letExpr () (BPat () (varPat () "r"))
--                    (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) 
--                        (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a"))
--                , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" []))
--                ]

--    -- (let r = { a = 1, b = 2 } in ({ a = a | z }) => z)({ a = 5 ))
--
--    expr = 
--            appExpr () 
--                [ letExpr () (BPat () (varPat () "r"))
--                    (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) 
--                        (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z"))
--                , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" []))
--                ]


--    expr = 
--        (fixExpr () "foldSucc"
--            (lamExpr () [varPat () "g", varPat () "a"] (funExpr () 
--                [ Clause () [conPat () "Succ" [varPat () "n"]] 
--                    [Guard [] (appExpr () 
--                        [ varExpr () "foldSucc"
--                        , varExpr () "g"
--                        , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"]
--                        , varExpr () "n"
--                        ])]
--                , Clause () [anyPat ()] 
--                    [Guard [] (varExpr () "a")]
--                ]))
--            (appExpr () 
--                [ varExpr () "foldSucc"
--                , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
--                , annExpr tInt (litExpr () (TInteger 0))
--                , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]]
--                ]))
--

--    testTree :: ProgExpr () 
--    testTree =
--        conExpr () "Node" 
--            [ annExpr tInt (litExpr () (TInteger 5))
--            , conExpr () "Node" 
--                [ annExpr tInt (litExpr () (TInteger 3)) 
--                , conExpr () "Node" 
--                    [ annExpr tInt (litExpr () (TInteger 2))
--                    , conExpr () "Leaf" []
--                    , conExpr () "Leaf" []
--                    ]
--                , conExpr () "Node" 
--                    [ annExpr tInt (litExpr () (TInteger 1))
--                    , conExpr () "Node" 
--                        [ annExpr tInt (litExpr () (TInteger 4))
--                        , conExpr () "Leaf" []
--                        , conExpr () "Leaf" []
--                        ]
--                    , conExpr () "Node" 
--                        [ annExpr tInt (litExpr () (TInteger 7))
--                        , conExpr () "Node" 
--                            [ annExpr tInt (litExpr () (TInteger 8))
--                            , conExpr () "Leaf" []
--                            , conExpr () "Leaf" []
--                            ]
--                        , conExpr () "Leaf" []
--                        ]
--                    ]
--                ]
--            , conExpr () "Node" 
--                [ annExpr tInt (litExpr () (TInteger 6)) 
--                , conExpr () "Node" 
--                    [ annExpr tInt (litExpr () (TInteger 2))
--                    , conExpr () "Leaf" []
--                    , conExpr () "Leaf" []
--                    ]
--                , conExpr () "Node" 
--                    [ annExpr tInt (litExpr () (TInteger 8))
--                    , conExpr () "Leaf" []
--                    , conExpr () "Leaf" []
--                    ]
--                ]
--            ]
--
--    expr = 
--      letExpr () 
--          (BPat () (varPat () "testTree")) testTree
--          (fixExpr () "loopTree"
--              (lamExpr () [varPat () "g", varPat () "t"] (patExpr () (varExpr () "t")
--                  [ Clause () [conPat () "Node" [varPat () "n", varPat () "t1", varPat () "t2"]] 
--                        [Guard [] (appExpr () [varExpr () "g", conExpr () "Node'" [varExpr () "n", varExpr () "t1", varExpr () "t2", appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t1"], appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t2"]]])]
--                  , Clause () [conPat () "Leaf" []] 
--                        [Guard [] (appExpr () [varExpr () "g", conExpr () "Leaf'" []])]
--                  ]))
--              (appExpr () 
--                  [ varExpr () "loopTree"
--                  , funExpr () 
--                      [ Clause () [conPat () "Node'" [varPat () "n", varPat () "t1", varPat () "t2", varPat () "a", varPat () "b"]] [Guard [] (op2Expr () (OAdd ()) (varExpr () "n") (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))]
--                      , Clause () [conPat () "Leaf'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))]
--                      ]
--                  , varExpr () "testTree"
--                  ]))


--    -- 5 factorial
--    expr = 
--        (fixExpr () "foldSucc"
--            (lamExpr () [varPat () "g", varPat () "a"] (funExpr () 
--                [ Clause () [conPat () "Succ" [varPat () "n"]] 
--                    [Guard [] (appExpr () 
--                        [ varExpr () "foldSucc"
--                        , varExpr () "g"
--                        , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"]
--                        , varExpr () "n"
--                        ])]
--                , Clause () [anyPat ()] 
--                    [Guard [] (varExpr () "a")]
--                ]))
--            (letExpr () 
--                (BFun () "toInt" [varPat () "n"])
--                (appExpr () 
--                    [ varExpr () "foldSucc"
--                    , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
--                    , annExpr tInt (litExpr () (TInteger 0))
--                    , varExpr () "n"
--                    ])
--                (appExpr () 
--                    [ varExpr () "foldSucc"
--                    , lamExpr () [varPat () "n", varPat () "x"] (op2Expr () (OMul ()) (appExpr () [varExpr () "toInt", varExpr () "n"]) (varExpr () "x"))
--                    , annExpr tInt (litExpr () (TInteger 1))
--                    , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]]]]
--                    ])))


    expr =
        appExpr ()
            [ op2Expr () (OAdd ()) (holeExpr ()) (holeExpr ())
            , annExpr tInt (litExpr () (TInteger 5))
            , annExpr tInt (litExpr () (TInteger 5))
            ]



--    expr = Fix (EApp () [Fix (EOp2 () (OAdd ()) (Fix (EVar () "z")) (Fix (EVar () "zz"))),Fix (ELit () (TInteger 5)),Fix (ELit () (TInteger 3))])


--    expr = 
--        (fixExpr () "map" 
--            (lamExpr () [varPat () "f"]
--                (funExpr () 
--                    [ Clause () [conPat () "[]" []] 
--                          [ Guard [] (conExpr () "[]" [])
--                          ]
--                    , Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
--                          [ Guard [] (conExpr () "(::)" 
--                              [ appExpr () [varExpr () "f", varExpr () "x"]
--                              , appExpr () [varExpr () "map", varExpr () "f", varExpr () "xs"]
--                              ])
--                          ]]))
--            (appExpr () 
--                [ varExpr () "map"
--                , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
--                , annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3)])
--                ]))
--

--    -- let r = { a = 1, b = 2, c = 3 } in (({ a = a | z }) => z)(r)
--
--    expr = letExpr () (BPat () (varPat () "r"))
--               (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "c" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" []))))) 
--                        (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
--                                    , varExpr () "r" ])


--    -- (({ a = a | z }) => z)({ a = 1, b = 2, d = 3 })
--
--    expr = appExpr () 
--        -- [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
--        [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
--        , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) 
--                        (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) 
--                        (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) 
--                        (conExpr () "{}" [])))) ]
--

--    -- (({ a = a | z }) => z)({ a = 1 })
--
--    expr = appExpr () 
--        -- [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
--        [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
--        , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" [])) 
--        ]


--    -- ({ a = a | z }) => z
--
--    expr = 
--        -- [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
--        lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")


--    -- (z) => { a = 1 : Int | z }
--
--    expr = 
--        lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" 
--            (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))


--    -- ((z) => { a = 1 : Int | z })({ b = 2 })
--
--    expr = 
--        appExpr () [
--            lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" 
--                (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))
--        , recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))
--        ]

--    -- let f = (z) => { a = 1 : Int | z } in f({ b = 2 })
--
--    expr = 
--
--        letExpr () 
--            (BPat () (varPat () "f"))
--            (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))) 
--            (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])

--    -- let f(z) = { a = 1 : Int | z } in f({ b = 2 })
--
--    expr = 
--
--        letExpr () 
--            (BFun () "f" [varPat () "z"])
--            (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) 
--            (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])



--        appExpr () [
--            lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))
--        , recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))
--        ]

--    expr = funExpr () 
--        [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] 
--            [Guard [] (litExpr () (TBool True))]
--        , Clause () [conPat () "[]" []] 
--            [Guard [] (litExpr () (TBool True))]
--        , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] 
--            [Guard [] (litExpr () (TBool True))]
--        ]


--    expr = 
--        (lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))


--    -- ((a, b) => a + b)(5 : Int, 3)
--    expr = 
--        appExpr () 
--            [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b"))
--            , annExpr tInt (litExpr () (TInteger 5))
--            , litExpr () (TInteger 3) ]

--    expr = 
--        appExpr () 
--            [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b"))
--            , annExpr tInt (litExpr () (TInteger 5))
--            , litExpr () (TInteger 3) ]



--    -- ((a, b) => a + b)(5, 3)
--    expr = 
--        appExpr () 
--            [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b"))
--            , litExpr () (TInteger 5)
--            , litExpr () (TInteger 3) ]


--    -- (a, b) => a + b
--    expr = 
--        (lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))


--    expr =
--        litExpr () (TInteger 1)


--    expr =
--        lamExpr () [varPat () "b"] (appExpr () [varExpr () "testFun1", varExpr () "b"])


--    expr =
--        lamExpr () [varPat () "a"] (op2Expr () (OEq ()) (varExpr () "a") (litExpr () (TInteger 1)))


--    expr =
--        (lamExpr () [varPat () "a"] (appExpr () [varExpr () "(==)", varExpr () "a", litExpr () (TInteger 1)]))


--    -- let 
--    --   withDefault(val)
--    --     | Some(y) => y
--    --     | None    => val
--    --   in
--    --     Some(3 : Int).withDefault(5 : Int)
--    expr = 
--        letExpr () (BFun () "withDefault" [varPat () "val"]) 
--            (funExpr () 
--                [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [] (varExpr () "y") ]
--                , Clause () [conPat () "None" []] [ Guard [] (varExpr () "val") ]
--                ])
--            (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TInteger 5))]) (conExpr () "Some" [annExpr tInt (litExpr () (TInteger 3))]))

--    -- let 
--    --   withDefault(val)
--    --     | Some(y) => y
--    --     | None    => val
--    --   in
--    --     None.withDefault(5 : Int)
--    expr = 
--        letExpr () (BFun () "withDefault" [varPat () "val"]) 
--            (funExpr () 
--                [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [] (varExpr () "y") ]
--                , Clause () [conPat () "None" []] [ Guard [] (varExpr () "val") ]
--                ])
--            (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TInteger 5))]) (conExpr () "None" []))


--    -- let 
--    --   withDefault(val)
--    --     | Some(y) => y
--    --     | None    => val
--    --   in
--    --     withDefault
--    expr = 
--        letExpr () (BFun () "withDefault" [varPat () "val"]) 
--            (funExpr () 
--                [ Clause () (conPat () "Some" [varPat () "y"]) [ Guard [] (varExpr () "y") ]
--                , Clause () (conPat () "None" []) [ Guard [] (varExpr () "val") ]
--                ])
--            (varExpr () "withDefault")


--    -- 
--    --   val => fun
--    --     | Some(y) => y
--    --     | None    => val
--    expr = 
--            (lamExpr () [varPat () "val"] (funExpr () 
--                [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [] (varExpr () "y") ]
--                , Clause () [conPat () "None" []] [ Guard [] (varExpr () "val") ]
--                ]))



    -- ******************************************************************************************************************************************************************************************************

--    expr =
--        (funExpr () 
--            [ Clause () [varPat () "x"] [Guard [] (litExpr () (TInteger 3))]
--            ])


    -- TEST_EXPR_1

--    -- let 
--    --   fn
--    --     | Some(y) 
--    --         when(y == 1) => 1
--    --         when(y == 2) => 2
--    --         otherwise   => 3
--    --     | None          => 0
--    --   in
--    --     fn(Some(100))
--    expr = 
--        letExpr () (BPat () (varPat () "fn")) -- [annPat tInt (varPat () "val")]) 
--            (funExpr () 
--                [ Clause () [conPat () "Some" [varPat () "y"]] 
--                    [ Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1))
--                    , Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2))
--                    , Guard [] (litExpr () (TInteger 4))
--                    ]
--                , Clause () [conPat () "None" []] [ Guard [] (annExpr tInt (litExpr () (TInteger 0))) ]
--                ])
--            --(appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TInteger 100))]])
--            --(appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]])
--            --(appExpr () [varExpr () "fn", conExpr () "None" []])
--            (appExpr () [varExpr () "fn", annExpr (tApp kTyp (tCon kFun "Option") tInt) (conExpr () "None" [])])

    -- ******************************************************************************************************************************************************************************************************




--    testList =
--        annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)])
--
--    -- sum the list
--    expr = 
--      letExpr () 
--          (BPat () (varPat () "testList")) testList
--          (fixExpr () "loopList"
--              (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys")
--                  [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
--                        [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])]
--                  , Clause () [conPat () "[]" []] 
--                        [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])]
--                  ]))
--              --
--              -- loopList(fun | Cons'(x, xs, a) => x + a | Nil' => 0 : Int, testList)
--              -- 
--              (appExpr () 
--                  [ varExpr () "loopList"
--                  , funExpr () 
--                      [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Guard [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "a"))]
--                      , Clause () [conPat () "Nil'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))]
--                      ]
--                  , varExpr () "testList"
--                  ]))



--    testList =
--        annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)])
--
--    -- map over the list
--    expr = 
--      letExpr () 
--          (BPat () (varPat () "testList")) testList
--          (fixExpr () "loopList"
--              (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys")
--                  [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]]
--                        [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])]
--                  , Clause () [conPat () "[]" []] 
--                        [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])]
--                  ]))
--              --
--              -- let map = 
--              --
--              (letExpr ()
--                  (BFun () "map" [varPat () "f", varPat () "ys"])
--                  --
--                  -- ys.loopList(fun | Cons'(x, xs, a) => f(x) :: a | Nil' => [])
--                  -- 
--                  (op2Expr () (ODot ())
--                      (appExpr () 
--                          [ varExpr () "loopList"
--                          , funExpr () 
--                              [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Guard [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], varExpr () "a"])]
--                              , Clause () [conPat () "Nil'" []] [Guard [] (conExpr () "[]" [])]
--                              ]
--                          ])
--                      (varExpr () "ys"))
--
--                  (appExpr () 
--                      [ varExpr () "map"
--                      , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1)))
--                      , testList
--                      ])))


--    expr = r
--      where
--        Right r = runParserStack exprParser "" "let xs = [5 : Int, 3, 3] in match xs with | [x] => x | [x, y] => x | [x, y, z] => x | _ => 0"

--    expr = r
--      where
--        Right r = runParserStack exprParser "" "let xs = [5 : Int, 3, 3, 3] in match xs with | [x] => x | [x, y] => x | [x, y, z] => x | _ => 0"

--    expr = r
--      where
--        Right r = runParserStack exprParser "" "let xs = [1 : Int,2,3] in match xs with | [x] or [x, _] or [x, _, _] => x | _ => 0"

--    expr = r
--      where
--        Right r = runParserStack exprParser "" "let xs = [] : List Int in match xs with | [x] or [x, _] or [x, _, _] => x | _ => 0"





--    expr = 
--        letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BFun () "add5" [varPat () "z"]) (appExpr () [varExpr () "add", varExpr () "z", annExpr tInt (litExpr () (TInteger 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TInteger 3))]))

--    expr = r
--      where
----        Right r = runParserStack exprParser "" "let xs = [] in match xs with | (x :: _) when(xs <= 3) => x | _ => 0"
--        Right r = runParserStack exprParser "" "let xs = [1] : List Int in match xs with | (x :: _) when(x == 1) => x | _ => 0"




--    -- DONE --
--    expr = r
--      where
--        Right r = runParserStack exprParser "" "{ a = { b = { c = \"d\" } } }.a.b.c"
--    -- DONE --



--    expr = 
--        letExpr () (BPat () (varPat () "f"))
--            --(appExpr () [varExpr () "(-)", holeExpr (), annExpr tInt (litExpr () (TInteger 3))])
--            (appExpr () [varExpr () "isLongerThan", holeExpr (), holeExpr ()])
----            (appExpr () [varExpr () "isLongerThan", holeExpr (), litExpr () (TString "boo")])
--            (appExpr () [varExpr () "f", litExpr () (TInteger 4)])

--    -- AMBIGUITY
--    -- AMBIGUITY
--    -- AMBIGUITY
--    expr =
--        letExpr () (BPat () (varPat () "x"))
--            (litExpr () (TInteger 11))
--            (lamExpr () [varPat () "x"]
--                (appExpr () [varExpr () "show", appExpr () [varExpr () "read", varExpr () "x"]]))
        


--    expr =
--        letExpr () (BFun () "f" [varPat () "x"])
--            (litExpr () (TInteger 11))
--            (lamExpr () [varPat () "x"]
--                (appExpr () [varExpr () "show", appExpr () [varExpr () "read", varExpr () "x"]]))
--        

--    expr =
--        letExpr () (BFun () "f" [varPat () "x"])
--            (appExpr () [varExpr () "(+)", varExpr () "x", annExpr tInt (litExpr () (TInteger 5))])
--            (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInteger 5))])
--        



-- *************************
-- *************************
-- *************************
-- *************************

--    expr = 
--        -- let f(x, y) = x - y
--        --  in 
--        --  let
--        --    pred = f(_, 1)
--        --   in
--        --   pred(11)
--        letExpr () 
--            (BFun () "f" [varPat () "x", varPat () "y"])
--            (op2Expr () (OSub ()) (varExpr () "x") (varExpr () "y"))
--            (letExpr () 
--                (BPat () (varPat () "pred"))
--
--                (appExpr () [varExpr () "f", holeExpr (), annExpr tInt (litExpr () (TInteger 1))])
--
----                (appExpr () [varExpr () "f", holeExpr (), litExpr () (TInteger 1)])
--                (appExpr () [varExpr () "pred", litExpr () (TInteger 11)])
--            )


--    expr = 
--        appExpr () [appExpr () [varExpr () "(+)", annExpr tInt (litExpr () (TInteger 5))], litExpr () (TInteger 5)]


--    expr =
--            (appExpr ()
--                [ lamExpr () 
--                    [varPat () "x", varPat () "y"]
--                    -- match (x, y) with
--                    --   | (1, x) or (x, 1) 
--                    --       when x /= 0 => x
--                    --       otherwise   => 0
--                    --   | _ => 100
--                    (patExpr () 
--                        (tupleExpr () [varExpr () "x", varExpr () "y"])
--                        -- [ Clause () (orPat () (tuplePat () [litPat () (TInteger 1), varPat () "x"]) (tuplePat () [varPat () "x", litPat () (TInteger 1)])) 
--                        -- [ Clause () (orPat () (tuplePat () [annPat tInt (litPat () (TInteger 1)), varPat () "x"]) (tuplePat () [varPat () "x", litPat () (TInteger 1)])) 
--                        [ Clause () [tuplePat () [annPat tInt (litPat () (TInteger 1)), varPat () "x"]]  
--                            [ Guard [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TInteger 0))] (varExpr () "x")
--                            , Guard [] (annExpr tInt (litExpr () (TInteger 0)))
--                            ]
--
----                        [ Clause () (tuplePat () [annPat tInt (litPat () (TInteger 1)), annPat tInt (varPat () "x")])  
----                            [ Guard [] (annExpr tInt (litExpr () (TInteger 0)))
----                            ]
--
--                        , Clause () [anyPat ()] [ Guard [] (annExpr tInt (litExpr () (TInteger 100))) ]
--                        ])
--                , litExpr () (TInteger 1)
--                , litExpr () (TInteger 5)
--                ])

--    expr = (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , 
--        Clause () [conPat () "[]" []] [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () 
--            [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Guard [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 5)])) (patExpr () (varExpr () "xs") 
--                [ Clause () [conPat () "(::)" [varPat () "x", anyPat ()]] [Guard [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () [anyPat ()] [Guard [] (litExpr () (TInteger 0))] ])))) 



--    --expr = r
--    --  where
--    --    Right r = runParserStack exprParser "" "let xs = [5 : Int] : List Int in match xs with | (x :: _) when (length(xs) <= 3) => x | _ => 0"
--    expr = 
--        (fixExpr () "loopList"
--            (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys")
--                [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] 
--                      [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])]
--                , Clause () [conPat () "[]" []] 
--                      [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])]
--                ]))
--            (letExpr ()
--                (BFun () "length" [varPat () "xs"])
--                --
--                -- xs.loopList(fun | Cons'(_, _, a) => 1 + a | Nil' => 0 : Int)
--                -- 
--                (op2Expr () (ODot ())
--                    (appExpr () 
--                        [ varExpr () "loopList"
--                        , funExpr () 
--                            [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Guard [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))]
--                            , Clause () [conPat () "Nil'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))]
--                            ]
--                        ])
--                    (varExpr () "xs"))
--                (letExpr () 
--                    (BPat () (varPat () "xs"))
--                    (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 2)]))
--                    (patExpr () (varExpr () "xs")
--                        [ Clause () [conPat () "(::)" [varPat () "x", anyPat ()]] [Guard [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")]
--
--                        -- [ Clause () [conPat () "(::)" [varPat () "x", anyPat ()]] [Guard [] (varExpr () "x")]
--                        , Clause () [anyPat ()] [Guard [] (litExpr () (TInteger 0))]
--                        ]))))



--    -- let r = { z = 1 } in { a = 1, b = 2, d = 3 | r }
--    expr = 
--        letExpr () (BPat () (varPat () "r"))
--            (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" []))) 
--                    (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) 
--                                    (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) 
--                                    (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) 
--
--                                    (appExpr () [varExpr () "_#", varExpr () "r"])))))
--
--                                    --(varExpr () "r")))))


--    expr = 
--        letExpr () 
--            (BFun () "f" [varPat () "x", varPat () "y"])
--            (annExpr tInt (litExpr () (TInteger 111)))
--            (varExpr () "f")
----            (appExpr () [varExpr () "f", holeExpr (), holeExpr ()]) -- annExpr tInt (litExpr () (TInteger 1))])
--
--
----                    (appExpr () [varExpr () "getA", varExpr () "r"])


--    expr = (Fix (ELam () [Fix (PCon () "#" [Fix (PRow () "a" (Fix (PVar () "a")) (Fix (PVar () "z")))])] (Fix (EVar () "z")))) 





-- {-# LANGUAGE FlexibleContexts      #-}
-- {-# LANGUAGE FlexibleInstances     #-}
-- {-# LANGUAGE LambdaCase            #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE OverloadedStrings     #-}
-- {-# LANGUAGE RecordWildCards       #-}
-- module Main where
-- 
-- import System.Environment 
-- import Control.Monad.Except
-- import Control.Monad.Identity
-- import Control.Monad.Reader
-- import Control.Monad.State
-- import Control.Monad.Supply
-- import Control.Monad.Writer
-- import Data.Aeson
-- import Data.Maybe (fromJust)
-- import Data.Text (unpack)
-- import Data.Tree.View (showTree)
-- import Tau.Compiler.Pipeline
-- import Tau.Compiler.Pipeline.Stage1
-- import Tau.Compiler.Pipeline.Stage2
-- import Tau.Compiler.Pipeline.Stage3
-- import Tau.Compiler.Pipeline.Stage4
-- import Tau.Compiler.Pipeline.Stage5
-- import Tau.Compiler.Pipeline.Stage6
-- import Tau.Parser
-- import Tau.Compiler.Error
-- import Tau.Compiler.Substitute
-- import Tau.Serialize
-- --import Tau.Compiler.Translate
-- import Tau.Compiler.Typecheck
-- import Tau.Compiler.Unify
-- import Tau.Core
-- import Tau.Env
-- import Tau.Eval
-- import Tau.Lang
-- import Tau.Pretty
-- import Tau.Prog
-- import Tau.Tooling
-- import Tau.Type
-- import Text.Megaparsec
-- import qualified Tau.Compiler.Substitute as Sub
-- import qualified Tau.Env as Env
-- import qualified Data.ByteString.Lazy as LBS
-- 
-- import qualified Tau.Compiler.Pipeline.Stage1 as Stage1
-- import qualified Tau.Compiler.Pipeline.Stage2 as Stage2
-- import qualified Tau.Compiler.Pipeline.Stage3 as Stage3
-- import qualified Tau.Compiler.Pipeline.Stage4 as Stage4
-- import qualified Tau.Compiler.Pipeline.Stage5 as Stage5
-- import qualified Tau.Compiler.Pipeline.Stage6 as Stage6
-- 
-- 
-- instance Typed (Maybe Type) where
--     typeOf (Just t) = t
--     typeOf Nothing  = tVar (kVar "k") "a"
-- 
-- 
-- xxx5 :: Either UnificationError (Substitution Type, Substitution Kind)
-- xxx5 = fromJust (runExceptT (evalSupplyT xxx1 (numSupply "")))
-- 
-- --xxx1 :: (MonadFail m, MonadError UnificationError m) => m (Substitution Type, Substitution Kind)
-- xxx1 = unifyTypes 
--         (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
--         (tRow "shoeSize" tFloat (tRow "id" tInt (tVar kRow "r")))
-- 
-- 
--------------------------
--------------------------
--------------------------

data TypeFocus
    = TAppLeft  Kind Type
    | TAppRight Kind Type
    | TArrLeft  Type
    | TArrRight Type
    deriving (Show, Eq)

type TypeZipper = (Type, [TypeFocus])

tAppLeft :: TypeZipper -> Maybe TypeZipper
tAppLeft (Fix (TApp k l r), fs) = Just (l, TAppLeft k r:fs)
tAppLeft _ = Nothing

tAppRight :: TypeZipper -> Maybe TypeZipper
tAppRight (Fix (TApp k l r), fs) = Just (r, TAppRight k l:fs)
tAppRight _ = Nothing

tAppUp :: TypeZipper -> Maybe TypeZipper
tAppUp (t, TAppLeft  k r:fs) = Just (tApp k t r, fs)
tAppUp (t, TAppRight k l:fs) = Just (tApp k l t, fs)
tAppUp _ = Nothing

tArrLeft :: TypeZipper -> Maybe TypeZipper
tArrLeft (Fix (TArr l r), fs) = Just (l, TArrLeft r:fs)
tArrLeft _ = Nothing

tArrRight :: TypeZipper -> Maybe TypeZipper
tArrRight (Fix (TArr l r), fs) = Just (r, TArrRight l:fs)
tArrRight _ = Nothing

tArrUp :: TypeZipper -> Maybe TypeZipper
tArrUp (t, TArrLeft  r:fs) = Just (tArr t r, fs)
tArrUp (t, TArrRight l:fs) = Just (tArr l t, fs)
tArrUp _ = Nothing

-- ---- ----test3 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
-- ---- ----  where
-- ---- ----    r1 = tRow "name" tString (tRow "id" tInt tEmptyRow)
-- ---- ----    r2 = tRow "id" tString (tRow "name" tInt tEmptyRow)
-- ---- ----
-- ---- ----test4 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
-- ---- ----  where
-- ---- ----    r1 = tRow "name" tString (tRow "id" tInt tEmptyRow)
-- ---- ----    r2 = tRow "id" tInt (tRow "name" tString tEmptyRow)
-- ---- ----
-- ---- ----test5 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
-- ---- ----  where
-- ---- ----    r1 = tRow "x" tInt (tVar kRow "r")
-- ---- ----    r2 = tRow "x" tInt (tVar kRow "r")
-- ---- ----
-- ---- ----test6 = unifyRows (typeToRowX r1) (typeToRowX r2) :: Either UnificationError TypeSubstitution
-- ---- ----
-- ---- ----r1 = tRow "x" tInt (tVar kRow "r")
-- ---- ----r2 = tRow "y" tInt (tVar kRow "r")
-- ---- ----
-- ---- ----
-- ---- ----pattern1 = recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)) 
-- ---- ----
-- ---- ------pattern1 = conPat () "Foo" [litPat () (TBool True), litPat () (TInt 5)]
-- ---- ------pattern1 = conPat () "Done" [litPat () (TInt 5), litPat () (TInt 5)]
-- ---- ------pattern1 = conPat () "Some" [litPat () (TInt 5), litPat () (TInt 5)]
-- ---- ------pattern1 = listPat () [litPat () (TBool True), litPat () TUnit]
-- ---- ------pattern1 = listPat () [litPat () (TBool True), litPat () (TInt 5)]
-- ---- ------pattern1 = asPat () "someX" (conPat () "Some" [varPat () "x"])
-- ---- ------pattern1 = (conPat () "Some" [varPat () "x"])
-- ---- --
-- ---- ----pattern1 = recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil))
-- ---- ----pattern1 = recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") rNil))
-- ---- --
-- ---- --pattern1 = tuplePat () [litPat () (TString "foo"), litPat () (TBool True)]
-- ---- --
-- ---- --test1 :: IO ()
-- ---- --test1 = 
-- ---- --    case runInfer mempty testClassEnv testTypeEnv testConstructorEnv (runWriterT (inferPattern pattern1)) of
-- ---- --        Left e -> error (show e)
-- ---- --        Right ((pat, vars), sub, context) -> do
-- ---- --            let TypeInfo{..} = patternTag (apply sub pat)
-- ---- --                vars' = apply sub <$$> vars
-- ---- --                sub1 = normalizer nodeType
-- ---- --                xx1 = apply sub1 nodeType
-- ---- --                xx2 = apply sub1 nodePredicates
-- ---- --                xx3 = apply sub1 <$$> vars'
-- ---- --              in do
-- ---- --                  print (apply sub (typeOf pat))
-- ---- --                  --print (normalize (apply sub (typeOf pat)))
-- ---- --                  --print sub
-- ---- --                  --print ">>>>"
-- ---- --                  --print nodeType 
-- ---- --                  --print nodePredicates
-- ---- --                  --print vars'
-- ---- --                  --print ">>>>"
-- ---- --                  --print xx1
-- ---- --                  --print xx2
-- ---- --                  --print xx3
-- ---- --                  pure ()
-- ---- --
-- ---- --expr1 = funExpr () 
-- ---- --    [ Clause [ varPat () "x" ] [ Guard [] (litExpr () (TInt 1)) ] 
-- ---- --    ]
-- ---- --
-- ---- --test2 :: IO ()
-- ---- --test2 = 
-- ---- --    case runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExpr expr1) of
-- ---- --        Left e -> error (show e)
-- ---- --        Right (expr, sub, context) -> do
-- ---- --            print (expr, sub, context)
-- ---- --            print "..."
-- ---- --            print (apply sub expr)
-- ---- --            print "///"
-- ---- --            print context
-- ---- --            --let TypeInfo{..} = exprTag (apply sub expr)
-- ---- --            --    sub1 = normalizer nodeType
-- ---- --            --    xx1 = apply sub1 nodeType
-- ---- --            --    xx2 = apply sub1 nodePredicates
-- ---- --            --  in do
-- ---- --            --    --  print (normalize (apply sub (typeOf pat)))
-- ---- --            --    --  print sub
-- ---- --            --    --  print ">>>>"
-- ---- --            --    print nodeType 
-- ---- --            --    print nodePredicates
-- ---- --            --    --  print vars'
-- ---- --            --    print ">>>>"
-- ---- --            --    print (pretty xx1)
-- ---- --            --    print (pretty xx2)
-- ---- --            --    pure ()
-- ---- 
-- ---- 
-- ---- -- fun | x => 5
-- ---- --test1 :: (ProgExpr (TypeInfo [Error]), TypeSubstitution, Context)
-- ---- test1 = do
-- ----     print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print z
-- ---- 
-- ----     let xxx = unpack . renderDoc <$> zz
-- ----     putStrLn (showTree xxx)
-- ---- 
-- ---- --    print (pretty (normalized (apply sub x)))
-- ----     print "=========="
-- ----   where
-- ---- 
-- ----     zz = simplifiedExprTree z
-- ----     z = fromJust (evalSupply (simplifyExpr y) (nameSupply "a"))
-- ----     y = astExpr (apply sub x)
-- ----     (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ----     e = inferAst (Ast (funExpr () [ Clause () [varPat () "x"] [Guard [] (litExpr () (TInt 5))] ]))
-- 
-- normalized :: Ast (TypeInfo e) -> Ast (TypeInfo e)
-- normalized ast = apply (normalizer (astTypeVars ast)) ast 
-- 
-- ---- --test2 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub p)
-- ---- --    print "=========="
-- ---- --    print (apply sub <$$> vars)
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    ((p, vars), sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferPattern (conPat () "Some" [varPat () "x"])
-- ---- --
-- ---- --
-- ---- --test3 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub p)
-- ---- --    print "=========="
-- ---- --    print (apply sub <$$> vars)
-- ---- --    print "=========="
-- ---- --    print sub
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    ((p, vars), sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferPattern (listPat () [litPat () (TBool True), varPat () "x"])
-- ---- --
-- ---- --
-- ---- --test4 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (normalized (apply sub x)))
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))
-- ---- --
-- ---- --
-- ---- --
-- ---- --test5 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (normalized (apply sub x)))
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (conExpr () "(::)" [litExpr () (TBool True), conExpr () "[]" []]))
-- ---- --
-- ---- --
-- ---- --
-- ---- --test6 = do
-- ---- --    print "----------"
-- ---- ----    print (apply sub x)
-- ---- --    print (pretty (normalized (apply sub x)))
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst
-- ---- --        (Ast (appExpr () 
-- ---- --            [ funExpr () [ Clause () [conPat () "Some" [litPat () (TBool True)] ] 
-- ---- --                [ Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3)), op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 1))
-- ---- --                , Guard [] (litExpr () (TInt 1))
-- ---- --                ] ]
-- ---- --            , conExpr () "Some" [litExpr () TUnit] ]))
-- ---- --
-- ---- --
-- ---- --test66 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (funExpr () [ Clause () [conPat () "Some" [litPat () (TBool True)] ] 
-- ---- --        [ Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
-- ---- --        , Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 2)) 
-- ---- --        , Guard [] (litExpr () (TInt 3)) 
-- ---- --        ] ]))
-- ---- --
-- ---- --test67 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    --
-- ---- --    let Ast e1 = typeOf <$> apply sub x
-- ---- --    let e2 = simplifyExpr e1
-- ---- --    print (e2)
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (patExpr () [varExpr () "xs"] [ Clause () [conPat () "Some" [litPat () (TBool True)] ] 
-- ---- --        [ Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 1)) 
-- ---- --        , Guard [op2Expr () (OEq ()) (litExpr () (TInt 5)) (litExpr () (TInt 3))] (litExpr () (TInt 2)) 
-- ---- --        , Guard [] (litExpr () (TInt 3)) 
-- ---- --        ] ]))
-- ---- --
-- ---- --
-- ---- --
-- ---- --
-- ---- ----test66 :: ProgExpr ()
-- ---- ----test66 = funExpr () 
-- ---- ----    [ Clause () [conPat () "Some" [litPat () (TBool True)], conPat () "Some" [litPat () (TBool True)] ] [Guard [] (litExpr () (TInt 1))] 
-- ---- ----    , Clause () [conPat () "Some" [litPat () (TBool True)] ] [Guard [op2Expr () (litExpr () (TInt 4)) (litExpr () (TInt 4))] (litExpr () (TInt 1))] 
-- ---- ----    ]
-- ---- --
-- ---- --
-- ---- --test7 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))
-- ---- --
-- ---- --
-- ---- --test8 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print ctx
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
-- ---- --
-- ---- --
-- ---- --test9 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print ctx
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (op2Expr () (OEq ()) (litExpr () (TInt 1)) (litExpr () (TInt 1))))
-- ---- --
-- ---- --
-- ---- --test10 =
-- ---- --    Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x"))
-- ---- --
-- ---- --
-- ---- --test11 =
-- ---- --    Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (varExpr () "x"))
-- ---- --
-- ---- --
-- ---- --test12 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print ctx
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () (TInt 1), litExpr () (TInt 1)])))
-- ---- --
-- ---- --
-- ---- --test14 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print ctx
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
-- ---- --
-- ---- --
-- ---- --test15 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    print ctx
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    e = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TBool True)]))
-- ---- 
-- --
-- ----test16 = do
-- ----    print "x"
-- ----    --print (pretty (apply sub x))
-- ----
-- ----    --let Ast e1 = typeOf <$> apply sub x
-- ----    let Ast e1 = const () <$> apply sub x
-- ----    let e2 = evalSupply (simplifyExpr e1) (nameSupply "a")
-- ----    print e2
-- --
-- ----   where
-- ----     (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv b)
-- ----     b = inferAst (Ast e)
-- ----     --c = apply sub x
-- ----     --d = simplifyExpr c
-- ---- --    print (apply sub x)
-- ----     --
-- ---- 
-- ----     e :: ProgExpr ()
-- ----     e = letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit, litExpr () TUnit])
-- ---- 
-- ---- 
-- ---- test17 = do
-- ----     print "y"
-- ----     let Ast e1 = typeOf <$> apply sub x
-- ----     let e2 = fromJust (evalSupply (simplifyExpr e1) (nameSupply "a"))
-- ----     let fff = simplifiedExprTree e2
-- ----     let xxx = unpack . renderDoc <$> fff
-- ----     putStrLn (showTree xxx)
-- ----     print (e2)
-- ---- 
-- ----   where
-- ----     (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv b)
-- ----     b = inferAst (Ast e)
-- ---- 
-- ----     e :: ProgExpr ()
-- ----     e = recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) rNil :: Row (ProgExpr ())))
-- ---- --    e = listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3)]
-- ---- 
-- ---- --    e = tupleExpr () [litExpr () (TInt 1), litExpr () (TString "Bob")]
-- ---- 
-- ---- test18 = desugarRow exprTag conExpr (rExt "name" (litExpr tString (TString "Bob")) (rExt "id" (litExpr tInt (TInt 1)) rNil :: Row (ProgExpr Type)))
-- ---- 
-- ---- test19 = desugarRow exprTag conExpr (rNil :: Row (ProgExpr Type))
-- ---- 
-- ---- test20 = desugarRow exprTag conExpr (rExt "id" (litExpr tInt (TInt 1)) rNil :: Row (ProgExpr Type))
-- ---- 
-- ---- test21 = desugarRow exprTag conExpr (rVar (varExpr (tCon kRow "a") "r") :: Row (ProgExpr Type))
-- ---- 
-- ---- --test16 = do
-- ---- --    print "----------"
-- ---- --    print (apply sub x)
-- ---- --    print (pretty (apply sub x))
-- ---- --    let (Ast e) = typeOf <$> apply sub x
-- ---- --        e1 = translateRecords e
-- ---- --    print e1
-- ---- --    print "=========="
-- ---- --  where
-- ---- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ---- --    --e = inferAst (Ast (recordExpr () (rExt "name" (litExpr () (TInt 1)) ((rExt "name" (litExpr () (TString "Foo")) (rExt "id" (litExpr () (TInt 123)) rNil :: Row (ProgExpr ())))))))
-- ---- --    e = inferAst (Ast (recordExpr () (rExt "id" (litExpr () (TInt 1)) rNil :: Row (ProgExpr ()))))
-- --
-- --test123 = do
-- --    print sub
-- --    print y
-- --  where
-- --    Ast y = apply sub x
-- --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- --    e = inferAst (Ast (e1 :: ProgExpr ()))
-- --    --e1 = op1Expr () (ONeg ()) (varExpr () "x")
-- --    --e1 = recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) rNil))
-- --    --e1 = (op2Expr () (OEq ()) (varExpr () "x") (varExpr () "y"))
-- --    e1 = recordExpr () (rExt "name" (litExpr () (TString "Bob")) (rExt "id" (litExpr () (TInt 1)) (rVar (varExpr () "r"))))
-- --
-- --
-- --test456 = simplifyExpr2 (lamExpr (ti (tInt `tArr` tInt `tArr` tString)) [varPat (ti tInt) "p", varPat (ti tInt) "q"] (litExpr (ti tString) (TString "abc")))
-- ----     let fff = simplifiedExprTree e2
-- --
-- ------test456_ = simplifyExpr2 (lamExpr () [varPat () "p"] (litExpr () (TString "abc")))
-- ----
-- ------test456 = simplifyExpr2 (lamExpr (ti (tInt `tArr` tString)) [varPat (ti tInt) "p"] (litExpr (ti tString) (TString "abc")))
-- ----
-- ----xxx123 :: Expr t t t t t t t t Void Void Void Void Void Void Void Void Name (ClauseA t (ProgPattern t)) -> SimplifiedExpr t
-- ----xxx123 = cata $ \case
-- ----    EVar    t var        -> varExpr t var
-- ----    ECon    t con es     -> conExpr t con es
-- ----    ELit    t prim       -> litExpr t prim
-- ----    EApp    t es         -> appExpr t es
-- ----    EFix    t name e1 e2 -> fixExpr t name e1 e2
-- ----    EIf     t e1 e2 e3   -> ifExpr  t e1 e2 e3
-- ----    EPat    t es cs      -> patExpr t es undefined
-- ----    ELam    t ps e       -> lamExpr t ps e
-- --
-- --
-- --ti :: Type -> TypeInfo [Error]
-- --ti t = TypeInfo t [] []
-- 
-- test1 = do -- case fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExprType expr1)) of
--     print "----------"
--     print (apply sub a)
--     print "=========="
-- --    Left e -> error (show e)
-- --    Right (expr, sub, context) -> do
-- --        print (expr, sub, context)
-- --        print "..."
-- --        print (apply sub expr)
--   where
--     (a, sub, _, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv expr)
--     expr = inferAst (Ast (varExpr () "x"))
-- 
-- 
-- --mapAst :: (a -> b) -> ProgExpr a -> ProgExpr b
-- mapAst f e = zz
--   where
--     xx = Ast e
--     yy = fmap f xx
--     zz = astExpr yy
-- 

-- --test2 = do -- case fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv (inferExprType expr1)) of
-- --    print "----------"
-- --    print (apply sub2 (apply sub a))
-- --    print "----------"
-- --    putStrLn (showTree h)
-- --    print "=========="
-- --    print xx
-- --    print "=========="
-- --    putStrLn (showTree zz)
-- --    print "=========="
-- --    putStrLn (showTree zz2)
-- --    print "=========="
-- --    putStrLn (showTree zz22)
-- --    print "=========="
-- --    putStrLn (showTree zz222)
-- ----    print "=========="
-- ----    print xx222
-- ----    print "=========="
-- ----    print xx2
-- ----    print "=========="
-- ----    print xx22
-- ----    print "=========="
-- ----    print xx222
-- ----    print "=========="
-- --    --putStrLn (showTree zz22)
-- --    --print "=========="
-- ----    print xx3
-- ----    print "=========="
-- ----    print (evalExpr xx3 testEvalEnv)
-- ----    print "=========="
-- --    --putStrLn (showTree zz123)
-- ----    Left e -> error (show e)
-- ----    Right (expr, sub, context) -> do
-- ----        print (expr, sub, context)
-- ----        print "..."
-- ----        print (apply sub expr)
-- --  where
-- ----    e :: ProgExpr (TypeInfo [Error])
-- ----    e = astExpr (apply sub a)
-- --
-- --    h = unpack . renderDoc <$> g
-- --    g = exprTree (astExpr ee)
-- --
-- --    f :: Ast Type
-- --    f = typeOf <$> (apply sub a)
-- --
-- --    ee :: Ast (TypeInfo [Error])
-- --    ee = apply sub a
-- --
-- --    eee :: Ast (TypeInfoT [Error] (Maybe Type))
-- --    eee = fmap (fmap Just) ee
-- --
-- --    --xx = simplifyExpr yyyy -- (astExpr ee)
-- --    --xx = simplifyExpr (astExpr ee)
-- ----    xx :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
-- --    xx = stage1 (astExpr eee)
-- --
-- ----    xx2 :: Stage3Expr (TypeInfoT [Error] (Maybe Type))
-- --    xx2 = stage3 xx
-- --
-- --    xx22 :: Stage4Expr (TypeInfoT [Error] (Maybe Type))
-- --    xx22 = stage4 xx2
-- --
-- --    xx22_ :: Stage5Expr (Maybe Type)
-- --    xx22_ = foo5 nodeType xx22
-- --
-- --    xx222 :: Stage6Expr (Maybe Type)
-- --    xx222 = fromJust $ evalSupply (stage6 xx22_) (nameSupply "$")
-- --
-- --    xx3 :: Core
-- --    xx3 = undefined -- runIdentity (toCore xx2)
-- --
-- --    xx123 :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
-- --    xx123 = fromJust (evalSupply (runReaderT (evalStateT (compileClasses xx) []) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)) (nameSupply ""))
-- --
-- ----    yyyy = mapAst (const ()) (astExpr ee)
-- --
-- --    yy = exprTree xx
-- --    zz = unpack . renderDoc <$> yy
-- --
-- --    yy2 = exprTree xx2
-- --    zz2 = unpack . renderDoc <$> yy2
-- --
-- --    yy22 = exprTree xx22
-- --    zz22 = unpack . renderDoc <$> yy22
-- --
-- --    yy222 = exprTree3 xx222
-- --    zz222 = unpack . renderDoc <$> yy222
-- --
-- --    yy123 = exprTree xx123
-- --    zz123 = unpack . renderDoc <$> yy123
-- --
-- --    (a, sub, sub2, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv expr)
-- --    expr = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))
-- 
-- --    expr = inferAst (Ast (varExpr () "(+)"))
-- 
-- --    expr = inferAst (Ast (litExpr () (TInt 5)))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit])))
-- 
-- --    expr = inferAst (Ast (varExpr () "(::)"))
-- 
-- --    expr = inferAst (Ast (appExpr () [varExpr () "(::)", litExpr () (TInt 5), conExpr () "[]" []]))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (varExpr () "id") (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TString "foo")], appExpr () [varExpr () "id", litExpr () (TInt 1)]])))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr ()  [varExpr () "f", litExpr () (TInt 1)])))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (varExpr () "f")))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "x", varPat () "y"] (varExpr () "y")))
-- 
-- --    expr = inferAst (Ast (funExpr () [ Clause () [varPat () "x"] [Guard [] (litExpr () (TBool True))] ]))
-- 
-- --    expr = inferAst (Ast (funExpr () [ Clause () [conPat () "Some" [varPat () "x"]] [Guard [] (litExpr () (TBool True))] ]))
-- 
-- 
-- 
-- --    expr = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3), litExpr () (TInt 4)]))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (appExpr () [varExpr () "id", litExpr () (TInt 5)])))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "a", varPat () "b"] (appExpr () [varExpr () "(,)", varExpr () "a", varExpr () "b"])))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TInt 5)], appExpr () [varExpr () "id", litExpr () (TBool True)]])))
-- 
-- --    expr = inferAst (Ast (patExpr () [litExpr () (TInt 5)] [Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]]))
-- 
-- --    expr = inferAst (Ast (patExpr () [litExpr () (TInt 4)] 
-- --             [ Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]
-- --             , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
-- --             ]))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] [Clause () [anyPat ()] [Guard [] (litExpr () (TInt 1))]])))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] 
-- --        [ Clause () [varPat () "y"] [Guard [] (litExpr () (TInt 1))] 
-- --        , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
-- --        ])))
-- 
-- test555, test556 :: Type
-- --test555 = Fix (TApp (Fix (KCon "Row")) (Fix (TApp (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))))) "{a}")) (Fix (TVar (Fix (KCon "*")) "a5")))) (Fix (TApp (Fix (KCon "Row")) (Fix (TApp (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))))) "{b}")) (Fix (TArr (Fix (TVar (Fix (KVar "k10")) "a11")) (Fix (TVar (Fix (KVar "k10")) "a11")))))) (Fix (TCon (Fix (KCon "Row")) "{}")))))
-- 
-- test555 = tRow "b" tInt (tRow "a" tString (tRow "c" tBool tRowNil))
-- 
-- test556 = tRow "b" tInt (tRow "a" tString (tRow "c" tBool (tVar kRow "x")))
-- 
-- --test555 = Fix (TApp (Fix (KCon "Row")) (Fix (TApp (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KArr (Fix (KCon "Row")) (Fix (KCon "Row")))))) "{b}")) (Fix (TCon (Fix (KCon "*")) "Int")))) (Fix (TCon (Fix (KCon "Row")) "{}")))
-- 
-- test123 expr = do
--     let xx = toRep (astExpr ee)
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData2.json" (encode xx)
--     let xx1 = toRep ef
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData3.json" (encode xx1)
--     let xx2 = toRep eh
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData4.json" (encode xx2)
--     let xx3 = toRep ei
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData5.json" (encode xx3)
--     let xx4 = toRep ej
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData6.json" (encode xx4)
--     let xx5 = toRep ek
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData7.json" (encode xx5)
--     let xx6 = toRep el
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData8.json" (encode xx6)
--     let xx7 = toRep em
--     print "***********"
--     print "***********"
--     print "***********"
--     print xx7
--     LBS.writeFile "/home/laserpants/play/ast-folder-tree/ast-folder-tree/src/testData9.json" (encode xx7)
-- --    print a
-- --    putStrLn "---------------"
-- --    print ee
-- --    putStrLn "---------------"
-- --    print ef
-- --    putStrLn "---------------"
--     putStrLn "---------------"
--     putStrLn (showTree h)
--     putStrLn "---------------"
--     putStrLn (showTree h1)
--     putStrLn "---------------"
--     putStrLn (showTree h3)
--     putStrLn "---------------"
--     putStrLn (showTree h31)
--     putStrLn "---------------"
--     putStrLn (showTree h32)
--     putStrLn "---------------"
--     putStrLn (showTree h4)
--     putStrLn "---------------"
--     print el
--     putStrLn "---------------"
--     print em
--     putStrLn "---------------"
-- --    print eh
-- 
-- --    putStrLn "---------------"
-- ----    xx2
--   where
--     ee :: Ast (TypeInfo [Error])
--     ee = apply sub2 (apply sub a)
-- 
--     eee :: Ast (TypeInfoT [Error] (Maybe Type))
--     eee = fmap (fmap Just) ee
-- 
--     ef = Stage1.translate (astExpr eee)
-- 
--     eg = Stage2.translate ef
-- 
--     eh :: Stage2.WorkingExpr (Maybe Type)
--     eh = fromJust (evalSupply (runReaderT (evalStateT eg []) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)) (numSupply "a"))
-- 
--     ei = fromJust (evalSupply (Stage3.translate eh) (numSupply "#"))
-- 
--     ej = Stage4.translate ei
-- 
--     ek = fromJust (evalSupply (Stage5.translate ej) (numSupply "a"))
-- 
--     el = runIdentity (Stage6.translate ek)
-- 
--     em = evalExpr el testEvalEnv
-- 
--     h3 = unpack . renderDoc <$> g3
--     g3 = exprTree eh
-- 
--     h31 = unpack . renderDoc <$> g31
--     g31 = exprTree ei
-- 
--     h32 = unpack . renderDoc <$> g32
--     g32 = exprTree ej
-- 
-- --    xx :: Stage1Expr (TypeInfoT [Error] (Maybe Type))
-- --    xx = Stage1.translate (astExpr eee)
-- 
--     h4 = unpack . renderDoc <$> g4
--     g4 = exprTree3 ek
-- 
-- --    xx22_ :: Stage5Expr (Maybe Type)
-- --    xx22_ = foo5 nodeType ek
-- 
--     h1 = unpack . renderDoc <$> g1
--     g1 = exprTree ef
-- --
--     h = unpack . renderDoc <$> g
--     g = exprTree (astExpr ee)
-- --
-- --    xx2 :: Stage3Expr (Maybe Type)
-- --    xx2 = Stage3.translate (mapExpr2 nodeType xx)
-- 
--     (a, sub, sub2, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv prog)
-- 
--     prog = inferAst (Ast expr)
-- 
-- --    expr :: ProgExpr ()
-- --    --expr = lamExpr () [varPat () "x", varPat () "y"] (appExpr () [varExpr () "(+)", varExpr () "x", varExpr () "y"])
-- 
-- --    expr :: ProgExpr ()
--     --expr = op2Expr () (OAdd ()) (litExpr () (TInt 1)) (litExpr () (TInt 2))
-- 
-- --    expr = letExpr () (BPat () (varPat () "v")) (op2Expr () (OAdd ()) (litExpr () (TInt 1)) (litExpr () (TInt 2))) ((op2Expr () (OAdd ()) (varExpr () "v") (litExpr () (TInt 2))))
-- 
-- --    expr = litExpr () (TInt 2)
-- 
-- --    expr = varExpr () "(+)"
-- 
-- --    expr = litExpr () (TInt 5)
-- 
-- --    expr = rowExpr () "name" (litExpr () (TString "Bob")) (Just (rowExpr () "id" (litExpr () (TInt 5)) Nothing))
-- 
-- --    expr = 
-- --        letExpr () (BPat () (varPat () "r")) (rowExpr () "isAdmin" (litExpr () (TBool True)) Nothing)
-- --        (rowExpr () "name" (litExpr () (TString "Bob")) (Just (rowExpr () "id" (annExpr tInt (litExpr () (TInt 1))) (Just (varExpr () "r")))))
-- 
-- --    expr = 
-- --        patExpr () [ litExpr () (TInt 5) ] 
-- --            [ Clause () [ litPat () (TInt 3) ] [ Guard [] (litExpr () (TBool True)) ]
-- --            , Clause () [ litPat () (TInt 5) ] [ Guard [] (litExpr () (TBool False)) ]
-- --            ]
-- --
-- --    expr = 
-- --        patExpr () ( conExpr () "Some" [litExpr () (TBool True)] ) 
-- --            [ Clause () ( conPat () "Some" [litPat () (TBool True)] ) [ Guard [] (annExpr tInt (litExpr () (TInt 1))) ]
-- --            , Clause () ( conPat () "Some" [litPat () (TBool False)] ) [ Guard [] (litExpr () (TInt 2)) ]
-- --            ]
-- --
-- 
-- --    expr = 
-- --        funExpr () 
-- --            [ Clause () [ recordPat () (rowPat () "name" (varPat () "a") Nothing) ] [Guard [] (litExpr () (TBool True))]
-- --            ]
-- 
-- --    expr = Fix (EAnn tInt (litExpr () (TInt 5)))
-- 
-- --    expr = Fix (ERow () [("a", litExpr () (TInt 5)), ("b", lamExpr () [varPat () "x"] (varExpr () "x"))])
-- 
-- --w    expr = patExpr () [ rowExpr () [("name", litExpr () (TString "Bob"))] ] 
-- --        [ Clause () [ rowPat () [("name", varPat () "a")] ] [ Guard [] (varExpr () "a") ] ]
-- 
--     -- match { id = 1, name = "Bob" } with
--     --   | { name = a } => a
--     --
--     --   | { name = a | _ } => a
--     --
--     --expr = patExpr () [ rowExpr () "id" (annExpr tInt (litExpr () (TInt 1))) (Just (rowExpr () "name" (litExpr () (TString "Bob")) Nothing)) ] 
-- ----    expr = patExpr () [ rowExpr () "id" (annExpr tInt (litExpr () (TInt 1))) (Just (rowExpr () "name" (litExpr () (TString "Bob")) Nothing)) ] 
-- ------            [ Clause () [ rowPat () "name" (varPat () "a") Nothing ] [ Guard [] (varExpr () "a") ] ]
-- ----            [ Clause () [ rowPat () "name" (varPat () "a") (Just (anyPat ())) ] [ Guard [] (varExpr () "a") ] ]
-- 
-- --    expr = patExpr () [ rowExpr () [("name", litExpr () (TString "Bob")), ("id", litExpr () (TBool True))] ] 
-- --        [ Clause () [rowPat () [("id", varPat () "b"), ("name", varPat () "a")]] [Guard [] (varExpr () "b")] ]
-- 
-- --    expr = Fix (ERow () [("a", litExpr () (TInt 5)), ("b", varExpr () "b")])
-- 
--     -- match { name = "Bob", id = True } with
--     --   | { id = b, name = a } => b
-- 
-- --    expr = letExpr () (BPat () (varPat () "x")) (rowExpr () [("id", litExpr () (TBool True))]) (rowExpr () [("name", litExpr () (TString "Bob")), ("*", varExpr () "x")])
-- 
-- --Guard [] (litExpr () (TInt 123))
-- 
-- --    expr = letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")
-- 
-- --    expr = letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")
-- 
-- --    expr = letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit])
-- 
-- --    expr = appExpr () 
-- --        [ letExpr () (BFun  () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr () [varExpr () "f", litExpr () TUnit])
-- --        , recordExpr () (rowCons () "fromInteger" (lamExpr () [varPat () "x"] (litExpr () (TInt 55))) (conExpr () "{}" [])) 
-- --        ]
-- 
-- --    expr = recordExpr () (rowCons () "fromInteger" (lamExpr () [varPat () "x"] (litExpr () (TInt 55))) (conExpr () "{}" [])) 
-- 
-- --    expr = inferAst (Ast (varExpr () "(::)"))
-- 
-- --    expr = inferAst (Ast (appExpr () [varExpr () "(::)", litExpr () (TInt 5), conExpr () "[]" []]))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (varExpr () "x")))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (varExpr () "id") (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TString "foo")], appExpr () [varExpr () "id", litExpr () (TInt 1)]])))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "x")) (litExpr () (TInt 5)) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1)))))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TInt 5)) (appExpr ()  [varExpr () "f", litExpr () (TInt 1)])))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TInt 5)) (varExpr () "f")))
-- 
-- --    expr = inferAst (Ast (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (litExpr () (TInt 5)) (varExpr () "f")))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "x", varPat () "y"] (varExpr () "y")))
-- 
-- --    expr = inferAst (Ast (funExpr () [ Clause () [varPat () "x"] [Guard [] (litExpr () (TBool True))] ]))
-- 
-- --    expr = inferAst (Ast (funExpr () [ Clause () [conPat () "Some" [varPat () "x"]] [Guard [] (litExpr () (TBool True))] ]))
-- 
-- 
-- 
-- --    expr = inferAst (Ast (listExpr () [litExpr () (TInt 1), litExpr () (TInt 2), litExpr () (TInt 3), litExpr () (TInt 4)]))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (appExpr () [varExpr () "id", litExpr () (TInt 5)])))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "a", varPat () "b"] (appExpr () [varExpr () "(,)", varExpr () "a", varExpr () "b"])))
-- 
-- --    expr = inferAst (Ast (letExpr () (BPat () (varPat () "id")) (lamExpr () [varPat () "x"] (varExpr () "x")) (tupleExpr () [appExpr () [varExpr () "id", litExpr () (TInt 5)], appExpr () [varExpr () "id", litExpr () (TBool True)]])))
-- 
-- --    expr = inferAst (Ast (patExpr () [litExpr () (TInt 5)] [Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]]))
-- 
-- --    expr = inferAst (Ast (patExpr () [litExpr () (TInt 4)] 
-- --             [ Clause () [litPat () (TInt 5)] [Guard [] (litExpr () (TInt 1))]
-- --             , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
-- --             ]))
-- 
-- --    expr = inferAst (Ast (lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] [Clause () [anyPat ()] [Guard [] (litExpr () (TInt 1))]])))
-- 
-- --    -- (\x => match x with | Some y => 1) (Some True)
-- --    expr = appExpr () [lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] 
-- --        [ Clause () [conPat () "Some" [varPat () "y"]] [Guard [] (annExpr tInt (litExpr () (TInt 1)))] 
-- --        , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
-- --        ]), conExpr () "Some" [litExpr () (TBool True)]]
-- 
-- --    -- (\x => match x with | Some y => 1) None
-- --    expr = appExpr () [lamExpr () [varPat () "x"] (patExpr () [varExpr () "x"] 
-- --        [ Clause () [conPat () "Some" [varPat () "y"]] [Guard [] (annExpr tInt (litExpr () (TInt 1)))] 
-- --        , Clause () [anyPat ()] [Guard [] (litExpr () (TInt 2))]
-- --        ]), conExpr () "None" []]
-- 
-- 
-- 
-- --test557 :: Either UnificationError (Substitution Type, Substitution Kind)
-- --test557 = unifyTypes 
-- --    (tRow "name" tString (tVar kRow "r"))
-- --    (tRow "name" tString (tRow "id" tInt))
-- 
-- 
-- --test554 :: Either UnificationError (Substitution Type, Substitution Kind)
-- --test554 = unifyTypes 
-- --    (tRow "name" tString (tVar kRow "r"))
-- --    -- { name : String | r }
-- --    (tRow "id" tInt (tRow "name" tString (tVar kRow "q")))
-- --    -- { name : String | { id : Int } | q }
-- --
-- --test557 :: Either UnificationError (Substitution Type, Substitution Kind)
-- --test557 = unifyTypes 
-- --    (tRow "name" tString (tVar kRow "r"))
-- --    -- { name : String | r }
-- --    (tRow "name" tString (tRow "id" tInt (tVar kRow "q")))
-- --    -- { name : String | { id : Int } | q }
-- --
-- --test558 :: Either UnificationError (Substitution Type, Substitution Kind)
-- --test558 = unifyTypes 
-- --    (tRow "name" tString (tVar kRow "r"))
-- --    -- { name : String | r }
-- --    (tRow "name" tString (tRow "id" tInt tRowNil))
-- --    -- { name : String | { id : Int } | {} }
-- --
-- --test559 :: Either UnificationError (Substitution Type, Substitution Kind)
-- --test559 = unifyTypes 
-- --    (tRow "id" tInt (tRow "name" tString tRowNil))
-- --    -- { id : Int | { name : String | {} } }
-- --    (tRow "name" tString (tRow "id" tInt tRowNil))
-- --    -- { name : String | { id : Int | {} } }
-- 
-- mapExpr2 :: (t -> u) -> WorkingExpr t -> WorkingExpr u
-- mapExpr2 f = cata $ \case
--     EVar    t var          -> varExpr    (f t) var
--     EApp    t es           -> appExpr    (f t) es
--     EFix    t name e1 e2   -> fixExpr    (f t) name e1 e2
--     ELam    t ps e         -> lamExpr    (f t) (mapPattern <$> ps) e
--     EIf     t e1 e2 e3     -> ifExpr     (f t) e1 e2 e3
--     EPat    t es cs        -> patExpr    (f t) es (mapClause <$> cs)
--     ELet    t bind e1 e2   -> letExpr    (f t) (mapBind bind) e1 e2
--   where
--     mapBind = \case
--         BPat    t p        -> BPat       (f t) (mapPattern p)
--         BFun    t name ps  -> BFun       (f t) name (mapPattern <$> ps)
-- 
--     mapClause = \case
--         SimplifiedClause t ps g -> SimplifiedClause (f t) (mapPattern <$> ps) g
-- 
--     mapPattern = cata $ \case
--         PVar    t var      -> varPat     (f t) var
--         PCon    t con ps   -> conPat     (f t) con ps
--         PLit    t prim     -> litPat     (f t) prim
--         PAs     t as p     -> asPat      (f t) as p
--         POr     t p q      -> orPat      (f t) p q
--         PAny    t          -> anyPat     (f t)
--         PTuple  t ps       -> tuplePat   (f t) ps
--         PList   t ps       -> listPat    (f t) ps
--         PRow    t lab p q  -> rowPat     (f t) lab p q
-- --            PRecord t row        -> recordPat  (f t) row
-- 
-- 
-- --foo5 :: (t -> u) -> Stage5.TargetExpr t -> Stage5.TargetExpr u
-- --foo5 f = cata $ \case
-- --    EVar    t var          -> varExpr    (f t) var
-- --    ECon    t con es       -> conExpr    (f t) con es
-- --    ELit    t prim         -> litExpr    (f t) prim
-- --    EApp    t es           -> appExpr    (f t) es
-- --    EFix    t name e1 e2   -> fixExpr    (f t) name e1 e2
-- --    ELam    t ps e         -> lamExpr    (f t) ps e
-- --    EIf     t e1 e2 e3     -> ifExpr     (f t) e1 e2 e3
-- --    EPat    t es cs        -> patExpr    (f t) es (mapClause <$> cs)
-- --  where
-- --    mapClause = \case
-- --        SimplifiedClause t ps g
-- --                           -> SimplifiedClause (f t) (mapPattern <$> ps) g
-- --    mapPattern = cata $ \case
-- --        PVar    t var      -> varPat     (f t) var
-- --        PCon    t con ps   -> conPat     (f t) con ps
-- --        PLit    t prim     -> litPat     (f t) prim
-- --        PAs     t as p     -> asPat      (f t) as p
-- --        POr     t p q      -> orPat      (f t) p q
-- --        PAny    t          -> anyPat     (f t)
-- 
-- 
-- --test3 = u :: Either UnificationError (Substitution Type, Substitution Kind)
-- --  where
-- ----    u = unifyTypes (tVar (kVar "k1") "a1") tInt
-- --
-- ----    u = unifyTypes (tVar kTyp "a1") tInt
-- ----    u = unifyTypes (tVar kTyp "a1") (tVar kTyp "a1" `tArr` tVar kTyp "a1")
-- --
-- --    u = unifyTypes (tVar (kArr (kVar "k1") (kVar "k1")) "a1") (tVar (kVar "k1") "a1")
-- --
-- ------ --test4 = do
-- ------ --    print "----------"
-- ------ --    print (apply sub x)
-- ------ --    print (pretty (normalized (apply sub x)))
-- ------ --    print "=========="
-- ------ --  where
-- ------ --    (x, sub, ctx) = fromJust (runInfer mempty testClassEnv testTypeEnv testConstructorEnv e)
-- ------ --    e = inferAst (Ast (appExpr () [varExpr () "id", litExpr () (TInt 5)]))
-- --
-- ----abc123 :: (MonadError UnificationError m) => m ()
-- ----abc123 = do
-- ----    sub <- unifyTypes tInt tInt
-- ----    let x = apply sub (tVar kTyp "a")
-- ----    pure ()
-- 
-- main :: IO ()
-- main = do
--     --[a] <- getArgs
--     --let a = "let f | Some(x) => x | None => 0 in f(Some(5))" -- f(Some(5))" 
--     --let a = "let f | Some(x) => x | None => 0 : Int in f(Some(123))" -- f(Some(5))" 
--     --let a = "let f | Some(x) => x | None => 0 : Int in Some(123).f" -- f(Some(5))" 
--     --let a = "let f(val) | Some(x) => x | None => val : Int in Some(123).f(5)" -- f(Some(5))" 
--     --let a = "let f(val) | Some(x) => x | None => val : Int in None.f(5)" -- f(Some(5))" 
--     --let a = "let f({ name = n | a }) = n in f({ name = \"Bob\", id = 1 : Int })" -- f(Some(5))" 
--     let a = "let b = { wat = \"not\" } in { a = True | b }" -- f(Some(5))" 
--     --let a = "let f({ name = n | a }) = a in f({ name = \"Bob\", id = 1 : Int })" -- f(Some(5))" 
--     case doParse (pack a) of
--         Right e -> test123 e
--   where
--     doParse a = runParser exprParser "" a
-- -- print "Main"


