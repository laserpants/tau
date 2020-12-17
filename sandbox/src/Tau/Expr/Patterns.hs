{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE DeriveFoldable   #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TemplateHaskell   #-}
module Tau.Expr.Patterns where

import Control.Applicative ((<|>))
import Control.Arrow
import Control.Monad
import Control.Monad.Extra (maybeM)
import Control.Monad.Free 
import Control.Monad.Trans.Free (FreeT(..))
import Control.Monad.Reader
import Control.Monad.Supply 
import Control.Monad.Writer
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.List.Extra (groupSortOn, groupBy)
import Data.Maybe (fromJust, maybeToList)
import Data.Set.Monad (Set)
import Data.Tuple.Extra (fst3, thd3)
import Debug.Trace
import Tau.Env
import Tau.Expr
import Tau.Type
import Tau.Type.Substitution
import Tau.Util
import qualified Control.Monad.Free as Monad
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

simplify 
  :: (Show t, MonadFail m, MonadSupply Name m) 
  => Expr t (Pattern t) (Pattern t) 
  -> m (Expr t (SimpleRep t) Name)
simplify = cata alg where
    alg = \case 
        EVar t var     -> pure (varExpr t var)
        ECon t con exs -> conExpr t con <$> sequence exs
        ELit t lit     -> pure (litExpr t lit)
        EApp t exs     -> appExpr t <$> sequence exs

        --
        --  let-expressions can only bind to simple variables (formal parameters)
        --
        ELet t (Fix (PVar _ var)) e1 e2 -> 
            letExpr t var <$> e1 <*> e2

        --
        --  The same restriction applies to lambdas
        --
        ELam t (Fix (PVar _ var)) e1 -> 
            lamExpr t var <$> e1 

        --
        --  Expressions like \5 => ..., let 5 = ..., or let _ = ... are not allowed
        --
        ELam _ (Fix PLit{}) _   -> error "Pattern not allowed"
        ELet _ (Fix PLit{}) _ _ -> error "Pattern not allowed"
        ELam _ (Fix PAny{}) _   -> error "Pattern not allowed"
        ELet _ (Fix PAny{}) _ _ -> error "Pattern not allowed"

        --
        --  Expressions like let C x = y in f x
        --  get translated to: match y with | C x => f x
        --
        ELet _ rep e1 e2 -> do
            expr <- e1
            body <- e2
            mexp <- compile [expr] [Equation [rep] [] body]
            maybe (error "Refutable pattern in let-binding") pure mexp

        --
        --  Lambda expressions like \C x => f x
        --  get translated to \$z => match $z with | C x => f x in $z
        --  where $z is a fresh variable
        --
        ELam t rep e1 -> do
            fresh <- supply
            body <- e1
            mexp <- compile [varExpr t fresh] [Equation [rep] [] body]
            case mexp of
                Nothing -> error "Refutable pattern in lambda function"
                Just expr -> pure (lamExpr t fresh expr)

        EIf t cond e1 e2 ->
            ifExpr t <$> cond <*> e1 <*> e2

        --
        --
        --
        EMat t exs eqs -> do
            mexp <- join (compile <$> sequence exs <*> traverse sequence eqs)
            maybe (error "Non-exhaustive patterns") pure mexp

        EOp t op ->
            simplifyOp t op

simplifyOp :: (MonadSupply Name m) => t -> Op (m (Expr t p q)) -> m (Expr t p q)
simplifyOp t (OEq  a b) = eqOp  t <$> a <*> b
simplifyOp t (OAnd a b) = andOp t <$> a <*> b
simplifyOp t (OOr  a b) = orOp  t <$> a <*> b

--
--
--
--
--
--

--xxx 
--  :: (MonadSupply Name m) => [Tagged [Equation (Pattern t) a]] 
--  -> m (Maybe (Expr t (SimpleRep t) Name))
--xxx = cata alg
--
--alg 
--  :: ListF (Tagged [Equation (Pattern t) a]) (m (Maybe (Expr t (SimpleRep t) Name))) 
--  -> m (Maybe (Expr t (SimpleRep t) Name))
--alg = \case
--    Cons (ConTag eqs) as ->
--        let xxx = eqs -- :: [Equation (Pattern t) a]
--            yyy = as -- :: Int
--        in
--        undefined
--
--    Cons (VarTag eqs) as ->
--        undefined
--
--    Nil ->
--        undefined
--
--compileGroup 
--  :: Tagged [Equation (Pattern t) (Expr t (SimpleRep t) Name)]
--  -> Maybe (Expr t (SimpleRep t) Name)
--  -> m (Maybe (Expr t (SimpleRep t) Name))
--compileGroup = undefined
--
--yyy 
--  :: [Equation (Pattern t) (Expr t (SimpleRep t) Name)]
--  -> m (Maybe (Expr t (SimpleRep t) Name))
--yyy = cata $ \case
--    Cons a b -> 
--        let zz1 = a -- :: Equation (Pattern t) (Expr t (SimpleRep t) Name)
--            zz2 = b -- :: m (Maybe (Expr t (SimpleRep t) Name))
--            zz3 = runSubst2 b a
--        in
--        undefined
--
--    Nil -> 
--        undefined
--
--runSubst2
--  :: m (Maybe (Expr t (SimpleRep t) Name))
--  -> Equation (Pattern t) (Expr t (SimpleRep t) Name)
--  -> Equation (Pattern t) (Expr t (SimpleRep t) Name)
--runSubst2 =
--    undefined
--
--compileVarGroup 
--  :: [Equation (Pattern t) (Expr t (SimpleRep t) Name)]
--  -> Expr t (SimpleRep t) Name
--  -> Maybe (Expr t (SimpleRep t) Name)
--  -> m (Maybe (Expr t (SimpleRep t) Name))
--compileVarGroup eqs u b = 
--    undefined
--  where
--    xxx = runSubst <$> eqs
--    --runSubst
--    --  --:: Expr t (SimpleRep t) Name 
--    --  :: Equation (Pattern t) (Expr t (SimpleRep t) Name)
--    --  -> Equation (Pattern t) (Expr t (SimpleRep t) Name)
--    runSubst (Equation (Fix (PVar _ name):ps) exs e) =
--        substitute name u <$> Equation ps exs e 
--
----    compileGroup (VarTag eqs) next = do 
----        this <- compile us (runSubst <$> eqs)
----        pure (this <|> next)
----      where
----        runSubst (Equation (Fix (PVar _ name):ps) exs e) =
----            substitute name u <$> Equation ps exs e 
--
----    compileGroup (VarTag eqs) next = do 
----        this <- compile us (runSubst <$> eqs)
----        pure (this <|> next)
----      where
----        runSubst (Equation (Fix (PVar _ name):ps) exs e) =
----            substitute name u <$> Equation ps exs e 

--yxx :: (MonadSupply Name m) => [Expr t (SimpleRep t) Name] -> [ConGroup t a] -> m b
--yxx (u:us) cgs = do
--    a <- traverse zz cgs
--    undefined
--  where
--    zz (ConGroup t con ar eqs) =
--        undefined

--- 
--- 
--- 
--- 
--- 
--- 





--bork :: Expr t (SimpleRep t) Name -> Expr t (SimpleRep t) Name
--bork e = futu xxx (Match [] [] e)
--
----xxx :: Match t a -> ExprF t (SimpleRep t) Name (Control.Monad.Free.Free (ExprF t (SimpleRep t) Name) (Match t a))
--
--xxx 
--  :: Match t (Expr t (SimpleRep t) Name) 
--  -> ExprF t (SimpleRep t) Name (Monad.Free (ExprF t (SimpleRep t) Name) (Match t (Expr t (SimpleRep t) Name)))
--xxx = \case 
--    Match [] [] e -> 
--        fork e
--
--fork 
--  :: Expr t (SimpleRep t) Name 
--  -> ExprF t (SimpleRep t) Name (Monad.Free (ExprF t (SimpleRep t) Name) (Match t (Expr t (SimpleRep t) Name)))
--fork a = 
--    ELet undefined undefined e1 undefined
--  where
--    e1 :: Monad.Free (ExprF t (SimpleRep t) Name) (Match t (Expr t (SimpleRep t) Name))
--    e1 = Monad.Free undefined 
--    
----    EMat undefined undefined undefined


-- nodups xs =
--     match xs with
--         | Nil                           => Nil                       (e1)
--         | Cons x Nil                    => Cons x Nil                (e2)
--         | Cons y (Cons x xs) [ y == x ] => foo (Cons x xs)           (e3)
--         | Cons y (Cons x xs)            => Cons y (foo (Cons x xs))  (e4)
-- 
-- 
--     Match [xs] 
--           [ ( [Nil]                []       Nil                      )
--           , ( [Cons x Nil]         []       Cons x Nil               )
--           , ( [Cons y (Cons x xs)] [x == y] foo (Cons x xs)          )
--           , ( [Cons y (Cons x xs)] []       Cons y (foo (Cons x xs)) )
--           ]
--           Fail
-- 
--         - Apply the Constructor Rule
-- 
--     Case xs 
--         [ ( Nil        , Match []       
--                                [ ( [], [], Nil ) ]         
--                                Fail 
--                                )
--         , ( Cons $1 $2 , Match [$1, $2] 
--                                [ ( [x, Nil]        []       Cons x Nil               )
--                                , ( [y, Cons x xs ] [x == y] foo (Cons x xs)          )
--                                , ( [y, Cons x xs ] []       Cons y (foo (Cons x xs)) )
--                                ] 
--                                Fail 
--                                )
--         ]
-- 
--         - First case: Apply the Empty Rule 
-- 
--         - Second case: Apply the Variable Rule
-- 
--     Case xs 
--         [ ( Nil        , Base Nil )
--         , ( Cons $1 $2 , Match [$2] 
--                                [ ( [Nil]        []        Cons $1 Nil               )
--                                , ( [Cons x xs ] [x == $1] foo (Cons x xs)           )
--                                , ( [Cons x xs ] []        Cons $1 (foo (Cons x xs)) )
--                                ] 
--                                Fail 
--                                )
--         ]
-- 
-- 
--         - Second case: Apply the Constructor Rule
-- 
--     Case xs 
--         [ ( Nil        , Base Nil )
--         , ( Cons $1 $2 , Case $2
--                              [ ( Nil        , Match [] 
--                                                     [ ( [], [], Cons $1 Nil ) ]
--                                                     Fail 
--                                                     ) 
--                              , ( Cons $3 $4 , Match [$3, $4] 
--                                                     [ ( [x, xs] [x == $1] foo (Cons x xs)           )           
--                                                     , ( [x, xs] []        Cons $1 (foo (Cons x xs)) ) 
--                                                     ]
--                                                     Fail
--                                                     )
--                              ]
--                              )
--         ]
-- 
-- 
--     Case xs 
--         [ ( Nil        , Base Nil )
--         , ( Cons $1 $2 , Case $2
--                              [ ( Nil        , Base (Cons $1 Nil) ) 
--                              , ( Cons $3 $4 , Match [$4] 
--                                                     [ ( [xs] [$3 == $1] foo (Cons $3 xs)           )           
--                                                     , ( [xs] []         Cons $1 (foo (Cons $3 xs)) ) 
--                                                     ]
--                                                     Fail
--                                                     )
--                              ]
--                              )
--         ]
-- 
-- 
--     Case xs 
--         [ ( Nil        , Base Nil )
--         , ( Cons $1 $2 , Case $2
--                              [ ( Nil        , Base (Cons $1 Nil) ) 
--                              , ( Cons $3 $4 , If ($3 == $1) 
--                                                  (foo (Cons $3 $4)) 
--                                                  (Match 
--                                                      [] 
--                                                      [ ( [] [] Cons $1 (foo (Cons $3 $4)) ) ]
--                                                      Fail
--                                                      )
--                              ]
--                              )
--         ]
-- 
-- 
--     Case xs 
--         [ ( Nil        , Base Nil )
--         , ( Cons $1 $2 , Case $2
--                              [ ( Nil        , Base (Cons $1 Nil) ) 
--                              , ( Cons $3 $4 , If ($3 == $1) 
--                                                  (foo (Cons $3 $4)) 
--                                                  (Cons $1 (foo (Cons $3 $4))) )
--                              ]
--                              )
--         ]
-- 
-- 
-- -----------------------------
-- --
-- 
-- mappairs f [] ys         = []
-- mappairs f (x:xs) []     = []
-- mappairs f (x:xs) (y:ys) = f x y : mappairs f xs ys
-- 
-- 
--     Match [u1, u2, u3]
--           [ ( [f, Nil, ys]              []       Nil )
--           , ( [f, Cons x xs, Nil]       []       Nil )
--           , ( [f, Cons x xs, Cons y;ys] []       Cons (f x y) (mappairs f xs ys) )
--           ]
--           Fail
-- 
-- 
--     Match [u2, u3]
--           [ ( [Nil, ys]              []       Nil )
--           , ( [Cons x xs, Nil]       []       Nil )
--           , ( [Cons x xs, Cons y ys] []       Cons (u1 x y) (mappairs u1 xs ys) )
--           ]
--           Fail
-- 
-- 
--     Case u2
--         [ ( Nil        , Match
--                             [ u3 ]
--                             [ ( [ys] [] Nil ) 
--                             ]
--                             Fail
--           )
--         , ( Cons $1 $2 , Match
--                             [$1, $2, u3]
--                             [ ( [x, xs, Nil]       [] Nil ) 
--                             , ( [x, xs, Cons y ys] [] (Cons (u1 x y) (mappairs u1 xs ys)) ) 
--                             ]
--                             Fail
--           )
--         ]
-- 
-- 
--     Case u2
--         [ ( Nil        , Match
--                             []
--                             [ ( [] [] Nil ) 
--                             ]
--                             Fail
--           )
--         , ( Cons $1 $2 , Match
--                             [$2, u3]
--                             [ ( [xs, Nil]       [] Nil ) 
--                             , ( [xs, Cons y ys] [] (Cons (u1 $1 y) (mappairs u1 xs ys)) ) 
--                             ]
--                             Fail
--           )
--         ]
-- 
-- 
--     Case u2
--         [ ( Nil        , Base Nil ) ]
--         , ( Cons $1 $2 , Match
--                             [u3]
--                             [ ( [Nil]       [] Nil ) 
--                             , ( [Cons y ys] [] (Cons (u1 $1 y) (mappairs u1 $2 ys)) ) 
--                             ]
--                             Fail
--           )
--         ]
-- 
-- 
--     Case u2
--         [ ( Nil        , Base Nil ) ]
--         , ( Cons $1 $2 , Case u3
--                             [ ( Nil        , Match 
--                                                  [ ( [] [] Nil )]
--                                                  Fail
--                               ) ]
--                             [ ( Cons $3 $4 , Match 
--                                                  [$3, $4]
--                                                  [ ( [y, ys] [] (Cons (u1 $1 y) (mappairs u1 $2 ys)) ) ]
--                                                  Fail
--                               ) ]
--                             ]
--           )
--         ]
-- 
-- 
--     Case u2
--         [ ( Nil        , Base Nil ) ]
--         , ( Cons $1 $2 , Case u3
--                             [ ( Nil        , Base Nil ) ]
--                             [ ( Cons $3 $4 , Match 
--                                                  [$4]
--                                                  [ ( [ys] [] (Cons (u1 $1 $3) (mappairs u1 $2 ys)) ) ]
--                                                  Fail
--                               ) ]
--                             ]
--           )
--         ]
-- 
-- 
--     Case u2
--         [ ( Nil        , Base Nil ) ]
--         , ( Cons $1 $2 , Case u3
--                             [ ( Nil        , Base Nil ) ]
--                             [ ( Cons $3 $4 , Match 
--                                                  []
--                                                  [ ( [] [] (Cons (u1 $1 $3) (mappairs u1 $2 $4)) ) ]
--                                                  Fail
--                               ) ]
--                             ]
--           )
--         ]
-- 
-- 
--     Case u2
--         [ ( Nil        , Base Nil ) ]
--         , ( Cons $1 $2 , Case u3
--                             [ ( Nil        , Base Nil ) ]
--                             [ ( Cons $3 $4 , Base (Cons (u1 $1 $3) (mappairs u1 $2 $4)) ) ]
--           )
--         ]
-- 
-- 
-- 
-- 
-- 
-- 
-- 
-- -----------------------------
-- --
-- 
--     Match [u1, u2]
--         [ ( [Cons x xs]   []    one )
--         , ( [y]           []    two )
--         ]
--         Fail
-- 
-- 
--     Match [u1, u2]
--         [ ( [Cons x xs] [] one ) ]
--         Match [u1, u2] 
--             [ ( [y] [] two ) ]
--             Fail
-- 
-- 
--     Case u1
--         [ ( Cons $1 $2 , Match [$1, $2] 
--                                [ ( [x, xs] [] one ) ] 
--                                (Match [u1, u2] 
--                                       [ ( [y] [] two ) ] 
--                                       Fail) 
--           ) 
--         ]
-- 
-- 
-- 
-- 
-- 
-- 
-- 


--evenIndicesF :: [Int] -> [Int]
--evenIndicesF = futu coalg where
----    coalg :: [Int] -> Base (ListF Int t) (Control.Monad.Free.Free (Base (ListF Int t)) [Int])
--    coalg list = 
--        case project list of
--            Nil -> Nil
--            Cons a s -> do
--                case project s of
--                    Nil -> Nil
--                    Cons h t -> Cons h (pure t)
--
--
------
--
--gfrun :: FSeed t -> FSeed t
--gfrun = gfutu xx coalg2 
--
--xx3 :: (Monad m, Functor f) => m (f a) -> f (m (f a))
--xx3 = undefined
--
--xx2 :: (Monad m, Functor f) => m (f a) -> f (m a)
--xx2 = undefined
--
--xx :: Supply Name (FSeedF t a) -> FSeedF t (Supply Name a)
--xx = undefined

--xx :: Supply Name (FSeedF t a) -> FSeedF t (Supply Name a)
--xx a = fmap (fmap g) b
--  where
----    g :: FSeedF t a -> a
--    g (G a) = a
--    g FFail = undefined

--    b :: FSeedF t (Supply Name (FSeedF t a))
--    b = G a

--ork :: FSeedF t a -> FSeed t 
--ork FFail = Fix FFail
--ork (FIf a b c) = Fix (FIf a nb undefined)
--  where
--    c = b -- :: a
--    nb = bork b -- undefined :: Fix (FSeedF t)
--
--bork :: a -> Fix (FSeedF t)
--bork = undefined

--br :: Supply Name (FSeedF t a) -> Supply Name (FSeedF t (Supply Name a))
--br = fmap (fmap pure)
--
--bg :: FSeedF t a -> FSeedF t (Supply Name a)
--bg = fmap pure
--
--rz :: a -> Supply Name a
--rz = pure
--
--gr :: Supply Name (FSeedF t (Supply Name a)) -> Supply Name (Supply Name (FSeedF t a))
--gr = fmap sequence
--
--hr :: Supply Name (Supply Name (FSeedF t a)) -> Supply Name (FSeedF t a)
--hr = join

--coalg2 :: FSeed t -> FSeedF t (FreeT (FSeedF t) (Supply Name) (FSeed t))
--coalg2 x = do
--    case project x of
--        FMatch (u:us) qs c -> do
--            FIf undefined (lift bork) undefined -- (undefined :: Int) -- (lift bork)
--            --xxdfz bork
--          where
--            bork :: Supply Name (FSeed t)
--            bork = do
--                x <- supplies 5
--                pure (Fix FFail)

--zz :: a -> f a
--zz = undefined
--
--xxdfz :: Supply Name a -> f (FreeT f (Supply Name) a)
--xxdfz x = zz (lift x)
--
--xxdfe :: (Monad m, Functor f) => m (Fix f) -> f (FreeT f m (Fix f))
--xxdfe b = undefined
----  where
----    dd = pure b
--
--xxdfg :: (Monad m) => m a -> FreeT f m a -- f (FreeT f m a)
--xxdfg = lift

--type X = Expr () (SimpleRep ()) Name
--type Y = Equation (Pattern ()) X
--
--data FromF a 
--    = FromMatch [X] [Y] a
--    deriving (Show, Functor, Foldable, Traversable)
--
--data ToF a 
--    = ToCase Int
--    | ToIf Int
--    | Zz a 
--    | ThisOrThat a a
--    deriving (Show, Functor, Foldable, Traversable)
--
--ontot :: From -> To
--ontot = cata alg where
--    alg = \case
--        FromMatch (u:us) qs c ->
--            case equationGroups qs of
--                [VarTag eqs] -> 
--                    Fix (Zz c)
--
--type From = Fix FromF
--type To   = Fix ToF
--
--fromTo :: From -> To
--fromTo = futu coalg7
--
--coalg7 = project >>> \case
--    FromMatch a b c ->
--        undefined
--        --Zz (Pure (Fix (FromMatch a b c)))
--        -- Cons n (Pure (Fix (Stuff (n - 1))))
--
--    FromMatch a b c  ->
--        ToCase undefined


--

data InpF a = 
    Stuff Int 
  deriving (Functor, Foldable, Traversable)

type Inp = Fix InpF

zrun4 :: Inp -> [Int]
zrun4 = futu coalg4

drup = zrun4 (Fix (Stuff 5))

coalg4 = project >>> \case
    Stuff 0 ->
        Nil -- [1,2,3]

    Stuff n ->
--      Cons n (Pure (Fix (Stuff (n - 1))))
        Cons n (Free Nil)


--

orun3 :: (MonadSupply Name m) => In -> Out m
orun3 = futu coalg5

coalg5 :: (MonadSupply Name m) => In -> OutF m (Monad.Free (OutF m) In)
coalg5 = project >>> \case
    AFail ->
        Fail

    AMatch [] [] _ ->
        Fail

    AMatch [] (Equation [] [] e:_) _ ->
        D e

    AMatch [] (Equation [] exs e:qs) c ->
        If (Free (D (foldr1 (andOp ()) exs))) 
           (Free (D e)) 
           (Pure (Fix (AMatch [] qs c)))
--           (Free (Grok (pure (Pure (Fix (AMatch [] qs c))))))
           --(Free (Defer (Pure (Fix (AMatch [] qs c)))))

--        If (foldr1 (andOp ()) exs) e 
--           (Free (Defer (Pure (Fix (AMatch [] qs c)))))

        --D (ifExpr () (foldr1 (andOp ()) exs) e (undefined :: Gex ()))

        --foldr baz (D undefined) exs

    AMatch (u:us) qs c ->
        case equationGroups qs of
            [VarTag eqs] -> 
                traceShow "----" $ trace (show u <> " : ") $ traceShow (runSubst <$> eqs) $ traceShow "<---" $
                  Grok (pure (Pure (Fix (AMatch us (runSubst <$> eqs) c))))

                -- Defer (Pure (Fix (AMatch us (runSubst <$> eqs) c)))
                  where
                    runSubst (Equation (Fix (PVar _ name):ps) exs e) = 
                        substitute name u <$> Equation ps exs e
                    runSubst e =
                        error (show e)

            [ConTag eqs] -> 
                --Case u (traverse toCase (conGroups eqs)) 

                --Case (Free (D u)) (traverse toCase (conGroups eqs)) 
                --  where
                --    toCase (ConGroup t con ps eqs) = do
                --        vars <- supplies (length ps)
                --        pure ( PCon t con vars
                --             , Pure (Fix (AMatch (combine ps vars <> us) eqs c)) )
                --    combine ps vs = 
                --        uncurry (varExpr . getPatternTag) <$> zip ps vs

                Grok $ do
                    -- zoo <- traverse toCase (conGroups eqs)
                    --pure (undefined :: Int)
                    traceShow "****" $ traceShow (conGroups eqs) $ traceShow "<***" $ 
                      Free . Suitcase (Free (D u)) <$> traverse toCase (conGroups eqs)
--                    Free <$> (traverse toCase (conGroups eqs) >>= pure . (Suitcase (Free (D u)) ))
                  where
                    toCase (ConGroup t con ps eqs) = do
                        vars <- supplies (length ps)
                        pure ( PCon t con vars
                             , Pure (Fix (AMatch (combine ps vars <> us) eqs c)) )
                    combine ps vs = 
                        uncurry (varExpr . getPatternTag) <$> zip ps vs

            mixed -> 
                traceShow "^^^^" $ traceShow (foldr fn (project c) (getEqs <$> mixed)) $
                  Grok (pure (Pure (Fix (foldr fn (project c) (getEqs <$> mixed)))))
                --Defer (Pure (Fix (foldr fn (project c) (getEqs <$> mixed))))
              where
                getEqs (ConTag a) = a
                getEqs (VarTag a) = a

                fn eqs a = AMatch (u:us) eqs (Fix a)



oestRun222 :: Expr () (SimpleRep ()) Name
oestRun222 = fromJust $ evalSupply oestRun22 (nameSupply "$")

oestRun22 :: Supply Name (Expr () (SimpleRep ()) Name)
oestRun22 = oork oestRun2

oork :: Out (Supply Name) -> Supply Name (Expr () (SimpleRep ()) Name)
oork = cata alg
  where
    alg = \case
        --Case a b -> do
        --    xx <- a
        --    fez <- b
        --    ts <- traverse (fmap getTag . snd) fez
        --    matExpr (head ts) [xx] <$> traverse fn fez

        --    --fez <- b
        --    --ts <- traverse (fmap getTag . snd) fez
        --    --matExpr (head ts) [a] <$> traverse fn fez
        --  where
        --    fn (rep, expr) = Equation [rep] [] <$> expr

        Suitcase a b -> do
            xx <- a
            yy <- traverse fn b
            ts <- traverse (fmap getTag . snd) b
            pure (matExpr (head ts) [xx] yy)
          where
            fn :: (SimpleRep (), Supply Name (Gex ())) -> Supply Name (Equation (SimpleRep ()) (Gex ()))
            fn (rep, expr) = do
                --let zzz = unfix expr :: Int
                --in
                Equation [rep] [] <$> expr

        Grok a -> do
            join a

        --Defer a ->
        --    a

        D a ->
            pure a

        If a b c -> do
            ifExpr () <$> a <*> b <*> c

            --let t = getTag <$> unfix b
            --ifExpr () a b <$> c

        Fail ->
            pure $ varExpr () "err" -- error "Fail"


oestRun2 :: (MonadSupply Name m) => Out m
oestRun2 = orun3 arg
  where
--    arg :: Monad m => FSeed m ()
    arg = embed $ AMatch 
        [ varExpr () "xs" ]
        [ Equation 
              [conPat () "Nil" []]  
              [] 
              (conExpr () "Nil" [])
        , Equation 
              [conPat () "Cons" [varPat () "x", conPat () "Nil" []]] 
              [] 
              (conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []])
        , Equation 
              [conPat () "Cons" [varPat () "y", conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
              [eqOp () (varExpr () "x") (varExpr () "y")] 
              (appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]])
        , Equation 
              [conPat () "Cons" [varPat () "y", conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
              [] 
              (conExpr () "Cons" [varExpr () "y", appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]]])
        ]
        (embed AFail)




oestRun333 :: Expr () (SimpleRep ()) Name
oestRun333 = fromJust $ evalSupply oestRun33 (nameSupply "$")

oestRun33 :: Supply Name (Expr () (SimpleRep ()) Name)
oestRun33 = oork oestRun3

oestRun3 :: (MonadSupply Name m) => Out m
oestRun3 = orun3 arg
  where
--    arg :: Monad m => FSeed m ()
    arg = embed $ AMatch 
        [ varExpr () "z" ]
        [ Equation 
              [conPat () "Just" [varPat () "x"]]  
              [eqOp () (varExpr () "x") (litExpr () (LInt 5))] 
              (varExpr () "y")
        , Equation 
              [varPat () "$_"]  
              [] 
              (varExpr () "z")
        ]
        (embed AFail)



frun3 :: GSeed t (Supply Name) -> GSeed t (Supply Name)
frun3 = futu coalg3

coalg3 :: GSeed t (Supply Name) -> GSeedF t (Supply Name) (Monad.Free (GSeedF t (Supply Name)) (GSeed t (Supply Name)))
coalg3 = project >>> \case
    GMatch (u:us) qs c ->
        case equationGroups qs of
            [VarTag eqs] -> 
                GMatch us (runSubst <$> eqs) (Pure c)
                  where
                    runSubst (Equation (Fix (PVar _ name):ps) exs e) = 
                        substitute name u <$> Equation ps exs e

            [ConTag eqs] -> 
                GCase u (traverse toCase (conGroups eqs)) 
                  where
                    toCase (ConGroup t con ps eqs) = do
                        vars <- supplies (length ps)
                        pure ( PCon t con vars
                             , Free (GMatch (combine ps vars <> us) eqs (Pure c)) )
                    combine ps vs = 
                        uncurry (varExpr . getPatternTag) <$> zip ps vs

            mixed -> 
                let fn eqs = GMatch (u:us) eqs . Fix
                 in Pure <$> foldr fn (unfix c) (getEqs <$> mixed)
              where
                getEqs (ConTag a) = a
                getEqs (VarTag a) = a

    GCase a b -> 
        GCase a (fmap (fmap Pure <$>) b)

    GIf a b c -> do 
        undefined
        --GIf a (Pure b) (Pure c)

    GFail -> 
        GFail


zork :: GSeed t (Supply Name) -> Supply Name (Expr t (SimpleRep t) Name)
zork = cata alg
  where
    alg = \case
        GFail ->
            --pure (varExpr () "xxx")
            error "Incomplete pattern"

        GMatch a b c -> do
            let d1 = a -- :: [Gex t]
            let d2 = b -- :: [Equation (Pattern t) (Gex t)]
            let d3 = c -- :: Supply Name (Expr t (SimpleRep t) Name)
            e3 <- c
            let gork = undefined 
            pure (matExpr undefined a gork)
            --traceShowM g
            --pure (varExpr () "yyy")
            --error "????"

        GCase a b -> do
            fez <- b
            ts <- traverse (fmap getTag . snd) fez
            matExpr (head ts) [a] <$> traverse fn fez
          where
            fn (rep, expr) = Equation [rep] [] <$> expr

        --GIf a b c -> do
        --    t <- getTag <$> b
        --    ifExpr t a <$> b <*> c


--fn2 :: [Equation (Pattern t) (Gex t)] -> GSeedF t (Supply Name) (Fix (GSeedF t (Supply Name))) -> GSeedF t (Supply Name) (Fix (GSeedF t (Supply Name))) 
--fn2 eqs = GMatch (u:us) eqs -- eqs undefined 

--groo :: Fix (GSeedF t (Supply Name)) -> GSeedF t (Supply Name) (Monad.Free (GSeedF t (Supply Name)) (GSeed t (Supply Name)))
--groo a = H c
--  where
--    c :: Monad.Free (GSeedF t (Supply Name)) (GSeed t (Supply Name))
--    c = undefined -- Pure b
----    b :: GSeedF t (Supply Name) (GSeed t (Supply Name))
--    b = unfix a

--bazoo 
--  :: [Equation (Pattern t) (Gex t)]
--  -> GSeed t (Supply Name)
--  -> Fix (GSeedF t (Supply Name)) -- GSeedF t (Supply Name) (Monad.Free (GSeedF t (Supply Name)) (GSeed t (Supply Name)))
--bazoo eqs x = Fix (GMatch undefined eqs x) -- eqs undefined 

-- \x y -> GMatch (u:us) x undefined

--fzrk :: [ConGroup t a] -> Supply Name [(SimpleRep t, Monad.Free (GSeedF t (Supply Name)) (GSeed t (Supply Name)))]  -- Monad.Free (GSeedF t (Supply Name [(SimpleRep t, a)]))
--fzrk = traverse fn2 
--
--bzrk :: [ConGroup t a]
--bzrk = undefined

--foo :: Monad.Free (GSeedF t (Supply Name)) (GSeed t (Supply Name))
--foo = undefined
--
--fn :: ConGroup t a -> Supply Name (SimpleRep t, a)
--fn (ConGroup t con ps eqs) = do
--    vars <- supplies (length ps)
--    undefined
--
--        --GMatch (u:us) qs c -> 
--        --    GBase $ do
--        --        b <- supplies 4
--        --        undefined
--
--        ----_ ->
--        --    let zoo = traverse fn (c
--        --    GCase undefined undefined
--
--
----

frun :: FSeed t -> FSeed t 
frun = futu coalg 

coalg :: FSeed t -> FSeedF t (Monad.Free (FSeedF t) (FSeed t))
coalg = project >>> \case
    FMatch (u:us) qs c ->
        case equationGroups qs of
            [VarTag eqs] -> 
                error "VARS"

            [ConTag eqs] -> 
                undefined
                --FCase u (zzz <$> conGroups eqs)

            mix -> 
                error "MIX"

        --FMatch exs eqs (Pure c)

    FCase ex css -> 
        FCase ex (second Pure <$> css)

    FBase ex ->
        FBase ex

    FIf cond tr fl ->
        FIf cond (Pure tr) (Pure fl)

    FFail ->
        FFail


--gork :: Monad m => FSeedF m t a
--gork = sequence bork
--
--bork :: (Traversable t, Monad m) => t (m a)
--bork = undefined


--coalg :: (MonadSupply Name m) => FSeed m t -> FSeedF m t (Monad.Free (FSeedF m t) (FSeed m t))

--bokdfa :: Monad m => c -> FSeedF m t a
--bokdfa = undefined
--
--baz :: (MonadSupply Name m) => m (SimpleRep ())
--baz = do
--    vars <- supplies 4
--    pure (PCon () "Xxx" vars)


----zzz :: (MonadSupply Name m) => ConGroup t (Ex m t) -> (SimpleRep t, Monad.Free (FSeedF m t) (FSeed m t))
--zzz (ConGroup t con ps eqs) = do
--    vars <- supplies (length ps)
--    pure (PCon t con vars)
----  where
----    xxx :: (MonadSupply Name m) => m a
----    xxx = do
----        vars <- supplies (length ps)
----        undefined



------

-- data Seed t 
--     = Match [Ex t] [Equation (Pattern t) (Ex t)] (Seed t)
--     | Case (Ex t) [(SimpleRep t, Seed t)]
--     | Base (Ex t)
--     | If (Ex t) (Seed t) (Seed t)
--     | Fail
--     deriving (Show)
-- --    | Tagged [Tagged [Equation (Pattern t) (Ex t)]]
-- --    | Group (ConGroup t (Ex t))
-- 
-- --    Match [xs] 
-- --          [ ( [Nil]                []       Nil                      )
-- --          , ( [Cons x Nil]         []       Cons x Nil               )
-- --          , ( [Cons y (Cons x xs)] [x == y] foo (Cons x xs)          )
-- --          , ( [Cons y (Cons x xs)] []       Cons y (foo (Cons x xs)) )
-- --          ]
-- --          Fail

gork = fromJust $ evalSupply (printG testRun2) (nameSupply "$")

printG :: GSeed () (Supply Name) -> Supply Name (String)
printG = cata $ \case
    GMatch a b c ->
        pure ("GMatch " <> show a)

    GCase a b -> do
        (x, y) <- unzip <$> b
        let d11 = x :: [SimpleRep ()]
        e11 <- sequence y -- :: [Supply Name String]
        let bork = zip d11 e11
        pure ("GCase " <> show a <> " " <> show bork) --  <> show grok)

    GIf a b c ->
        pure "GIf"

    GFail ->
        pure "GFail"

testRun222 :: Expr () (SimpleRep ()) Name
testRun222 = fromJust $ evalSupply testRun22 (nameSupply "$")

testRun22 :: Supply Name (Expr () (SimpleRep ()) Name)
testRun22 = zork testRun2

testRun2 :: GSeed () (Supply Name)
testRun2 = frun3 arg
  where
--    arg :: Monad m => FSeed m ()
    arg = embed $ GMatch 
        [ varExpr () "xs" ]
        [ Equation 
              [conPat () "Nil" []]  
              [] 
              (conExpr () "Nil" [])
        , Equation 
              [conPat () "Cons" [varPat () "x", conPat () "Nil" []]] 
              [] 
              (conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []])
        , Equation 
              [conPat () "Cons" [varPat () "y", conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
              [eqOp () (varExpr () "x") (varExpr () "y")] 
              (appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]])
        , Equation 
              [conPat () "Cons" [varPat () "y", conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
              [] 
              (conExpr () "Cons" [varExpr () "y", appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]]])
        ]
        (embed GFail)

--        [ Equation 
--              [conPat () "Nil" []]  
--              [] 
--              (conExpr () "Nil" [])
--        , Equation 
--              [conPat () "Cons" [varPat () "x", conPat () "Nil" []]] 
--              [] 
--              (conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []])
--        , Equation 
--              [conPat () "Cons" [conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
--              [eqOp () (varExpr () "x") (varExpr () "y")] 
--              (appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]])
--        , Equation 
--              [conPat () "Cons" [conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
--              [] 
--              (conExpr () "Cons" [varExpr () "y", appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]]])
--        ]
--        (Fix FFail)

--        [ varExpr () "xs" ]
--        [ Equation 
--              [conPat () "Nil" []]  
--              [] 
--              (conExpr () "Nil" [])
--        , Equation 
--              [conPat () "Cons" [varPat () "x", conPat () "Nil" []]] 
--              [] 
--              (conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []])
--        , Equation 
--              [conPat () "Cons" [conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
--              [eqOp () (varExpr () "x") (varExpr () "y")] 
--              (appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]])
--        , Equation 
--              [conPat () "Cons" [conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
--              [] 
--              (conExpr () "Cons" [varExpr () "y", appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]]])
--        ] 
--        Fail


--testRun = evalSupply (step arg) (nameSupply "$") where
--    arg = Match 
--        [ varExpr () "xs" ]
--        [ Equation 
--              [conPat () "Nil" []]  
--              [] 
--              (conExpr () "Nil" [])
--        , Equation 
--              [conPat () "Cons" [varPat () "x", conPat () "Nil" []]] 
--              [] 
--              (conExpr () "Cons" [varExpr () "x", conExpr () "Nil" []])
--        , Equation 
--              [conPat () "Cons" [conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
--              [eqOp () (varExpr () "x") (varExpr () "y")] 
--              (appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]])
--        , Equation 
--              [conPat () "Cons" [conPat () "Cons" [varPat () "x", varPat () "xs"]]] 
--              [] 
--              (conExpr () "Cons" [varExpr () "y", appExpr () [varExpr () "foo", conExpr () "Cons" [varExpr () "x", varExpr () "xs"]]])
--        ] 
--        Fail
--
--
--step :: (Show t, MonadSupply Name m) => Seed t -> m (Seed t)
--step seed =
--    case seed of
--        Match [] [Equation [] [] e] _ ->
--            pure (Base e)
--
--        Match (u:us) qs s -> 
--            case equationGroups qs of
--                [VarTag eqs] ->
--                    pure (Match us (runSubst <$> eqs) s)
--                  where
--                    runSubst (Equation (p:ps) exs e) =
--                        substitute name u <$> Equation ps exs e
--                      where
--                        Fix (PVar _ name) = p
--
--                [ConTag eqs] -> do
--                    css <- traverse toCase (conGroups eqs)
--                    step (Case u css)
--
--                    --Case u <$> traverse toCase (conGroups eqs)
--                  where
--                    toCase (ConGroup t con ps eqs) = do 
--                        vars <- supplies (length ps)
--                        pure ( PCon t con vars
--                             , Match (combine ps vars <> us) eqs s )
--
--                    combine ps vs = 
--                        uncurry (varExpr . getPatternTag) <$> zip ps vs
--
--                mixed -> 
--                    pure (foldr (Match (u:us)) s (getEqs <$> mixed))
--                  where
--                    getEqs (ConTag a) = a
--                    getEqs (VarTag a) = a
--
--        Case e css -> do
--            let (reps, seeds) = unzip css
--            fez <- traverse step seeds
--            let xxx = zip reps fez
--            pure (Case e xxx)
--
--        _ ->
--            traceShow (">>>> " <> show seed <> " <<<<<") $ pure Fail
--
--run
--  :: (MonadSupply Name m) 
--  => Seed t
----  -> Expr t (SimpleRep t) Name
--  -> m (Expr t (SimpleRep t) Name)
--run seed = 
--    case seed of
--        Match (u:us) qs s -> 
--            case equationGroups qs of
--                [VarTag eqs] ->
--                    run =<< newSeed
--                  where
--                    newSeed = 
--                        pure (Match us undefined s)
--
--                [ConTag eqs] ->
--                    run =<< newSeed
--                  where
--                    newSeed = Case u <$> traverse toCase (conGroups eqs)
--                    toCase (ConGroup t con ps eqs) = do 
--                        vars <- supplies (length ps)
--                        pure ( PCon t con vars
--                             , Match (varExpr undefined <$> vars) eqs s )
--
--                mixed -> 
--                    run newSeed 
--                  where
--                    newSeed = foldr (Match (u:us)) s (untag <$> mixed)
--                    untag (ConTag a) = a
--                    untag (VarTag a) = a
--
--        --Match [] [] s -> 
--        --    error "TODO"
--
--        --Match [] (Equation [] [] e:_) s -> 
--        --    undefined
--
--        --Match [] (Equation [] exs _:es) s -> 
--        --    undefined
--
--        --Match (u:us) qs s -> 
--        --    case equationGroups qs of
--        --        [VarTag eqs] ->
--        --            run =<< newSeed
--        --          where
--        --            newSeed = 
--        --                pure (Match us undefined s)
--
--        --        [ConTag eqs] ->
--        --            run =<< newSeed
--        --          where
--        --            newSeed = Case u <$> traverse toCase (conGroups eqs)
--        --            toCase (ConGroup t con ar eqs) = do 
--        --                vars <- supplies ar
--        --                pure ( PCon t con vars
--        --                     , Match (varExpr undefined <$> vars) eqs s )
--
--        --        mixed -> 
--        --            run newSeed 
--        --          where
--        --            newSeed = foldr (Match (u:us)) s (untag <$> mixed)
--        --            untag (ConTag a) = a
--        --            untag (VarTag a) = a



--- 
--- 
--- 

compile
  :: (MonadSupply Name m) 
  => [Expr t (SimpleRep t) Name]
  -> [Equation (Pattern t) (Expr t (SimpleRep t) Name)]
  -> m (Maybe (Expr t (SimpleRep t) Name))
compile [] [] = pure Nothing
compile [] (Equation [] []  e:_) = pure (Just e)
compile [] (Equation [] exs e:qs) = do
    mexp <- compile [] qs
    pure (ifExpr (getTag e) (foldr1 (\a -> andOp (getTag a) a) exs) e <$> mexp)
compile (u:us) qs = foldrM compileGroup Nothing (equationGroups qs)
  where
    compileGroup (ConTag eqs) next = do
        eqss <- traverse fn (conGroups eqs)
        pure $ case concat eqss <> [Equation [] [] a | a <- maybeToList next] of
            [] -> next
            eqs@(Equation _ _ e:_) -> Just (matExpr (getTag e) [u] eqs)
      where
        fn (ConGroup t con ps eqs) = do
            names <- supplies (length ps)
--            let vars = varExpr undefined <$> names -- TODO!!!!
            let vars = varExpr t <$> names
            -- TODO !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

            this <- compile (vars <> us) eqs
            pure (maybe [] (pure . Equation [PCon t con names] []) (this <|> next))

    compileGroup (VarTag eqs) next = do 
        this <- compile us (runSubst <$> eqs)
        pure (this <|> next)
      where
        runSubst (Equation (Fix (PVar _ name):ps) exs e) =
            substitute name u <$> Equation ps exs e 

substitute :: Name -> Expr t (SimpleRep t) Name -> Expr t (SimpleRep t) Name -> Expr t (SimpleRep t) Name
substitute name subst = para $ \case
    ELet t pat (_, e1) e2 -> letExpr t pat e1 e2'
      where 
        e2' | name == pat = fst e2
            | otherwise   = snd e2

    ELam t pat e1 -> lamExpr t pat e1'
      where
        e1' | name == pat = fst e1
            | otherwise   = snd e1

    EMat t exs eqs -> matExpr t (snd <$> exs) (substEq <$> eqs)
      where
        substEq eq@(Equation ps _ _) 
            | name `elem` free ps = fst <$> eq
            | otherwise           = snd <$> eq

    expr -> snd <$> expr & \case
        EVar t var 
            | name == var -> subst
            | otherwise   -> varExpr t var

        ECon t con exs -> conExpr t con exs
        ELit t lit     -> litExpr t lit
        EApp t exs     -> appExpr t exs
        EIf t c e1 e2  -> ifExpr  t c e1 e2
        EOp t op       -> substOp t op
  where
    substOp t = \case
        OEq  a b -> eqOp  t a b
        OAnd a b -> andOp t a b
        OOr  a b -> orOp  t a b

data Tagged a = ConTag a | VarTag a
    deriving (Show, Eq, Ord)

taggedEq :: Equation (Pattern t) a -> Tagged (Equation (Pattern t) a)
taggedEq eq@(Equation ps _ _) = 
    case project <$> ps of
        PCon{}:_ -> ConTag eq
        _        -> VarTag eq

equationGroups :: [Equation (Pattern t) a] -> [Tagged [Equation (Pattern t) a]]
equationGroups = cata alg . fmap taggedEq where
    alg Nil = []
    alg (Cons (ConTag e) (ConTag es:ts)) = ConTag (e:es):ts
    alg (Cons (VarTag e) (VarTag es:ts)) = VarTag (e:es):ts
    alg (Cons (ConTag e) ts) = ConTag [e]:ts
    alg (Cons (VarTag e) ts) = VarTag [e]:ts

data ConGroup t a = ConGroup t Name [Pattern t] [Equation (Pattern t) a]
    deriving (Show, Eq)

conGroups :: [Equation (Pattern t) a] -> [ConGroup t a]
conGroups =
    concatMap conGroup
      . groupSortOn (fst3 . snd)
      . concatMap expanded
  where
    conGroup all@((t, (con, ps, _)):_) = 
        [ConGroup t con ps (thd3 . snd <$> all)]
    conGroup [] = 
        []
    expanded (Equation (Fix (PCon t con ps):qs) exs e) =
        [(t, (con, ps, Equation (ps <> qs) exs e))]

--tagsMatch :: Tagged a -> Tagged b -> Bool
--tagsMatch (ConTag _) (ConTag _) = True
--tagsMatch (VarTag _) (VarTag _) = True
--tagsMatch _ _ = False


--    alg (Cons s (t:ts))
--        | tagsMatch s t = grok s t:ts
--        | otherwise = grok s []:t:ts

--equationGroups :: [SimpleEq t] -> [(Head, [SimpleEq t])]
--equationGroups = cata alg . fmap taggedEq 
--  where
--    alg :: Algebra (ListF (Head, SimpleEq t)) [(Head, [SimpleEq t])]
--    alg Nil =
--        []
--    alg (Cons (pt, eq) []) =
--        [(pt, [eq])]
--    alg (Cons (pt, eq) (group@(qt, eqs):gs))
--        | pt == qt  = (pt, eq:eqs):gs
--        | otherwise = (pure <$> taggedEq eq):group:gs
--
--    taggedEq eq = (headType eq, eq)

--conGroups :: [SimpleEq t] -> [(Name, [Rep t], t, [SimpleEq t])]
--conGroups =
--    concatMap conGroup
--      . groupSortOn (fst3 . fst)
--      . concatMap expanded
--  where
--    expanded (Equation (Fix (RCon t con rs):qs) c e) =
--        [((con, rs, t), Equation (rs <> qs) c e)]
--    expanded _ =
--        []
--    conGroup gs@(((con, rs, t), _):_) =
--        [(con, rs, t, snd <$> gs)]
--    conGroup [] =
--        []

--  :: (Eq t, MonadSupply Name m)
--  => [SimpleExpr t]
--  -> [SimpleEq t]
--  -> SimpleExpr t
--  -> m (SimpleExpr t)

--simplify :: (Eq t, MonadSupply Name m) => RepExpr t -> m (SimpleExpr t)
--simplify = cata alg where
--    alg = \case 
--        EVar t var -> pure (tagVar t var)
--        ELit t lit -> pure (tagLit t lit)
--        EApp t exs -> tagApp t <$> sequence exs
--        --
--        --  Expressions like  : let Just x = y in f x
--        --  get translated to : match y with | Just x => f x
--        --
--        ELet _ rep e1 e2 -> do
--            exp <- e1
--            ret <- e2
--            compileMatch [exp] [Equation [rep] [] ret] eErr
--        --
--        --  Lambda expressions like : \Just x => f x
--        --  get translated to       : \z => match z with | Just x => f x in z
--        --  where z is a fresh variable
--        --
--        ELam t rep ex -> do
--            fresh <- supply
--            ret <- ex
--            ex1 <- compileMatch [tagVar t fresh] [Equation [rep] [] ret] eErr
--            pure (tagLam t (sVar t fresh) ex1)
--
--        EMatch _ exs eqs -> 
--            join (compileMatch <$> sequence exs 
--                               <*> traverse sequenceEqExprs eqs 
--                               <*> pure eErr)
--
--    sequenceEqExprs
--      :: (Eq t, MonadSupply Name m) 
--      => Equation (Rep t) (m (SimpleExpr t)) 
--      -> m (SimpleEq t)
--    sequenceEqExprs (Equation ps exs e) = 
--        Equation ps <$> sequence exs <*> e
--
--compileMatch
--  :: (Eq t, MonadSupply Name m)
--  => [SimpleExpr t]
--  -> [SimpleEq t]
--  -> SimpleExpr t
--  -> m (SimpleExpr t)
--compileMatch [] [] d = pure d
--compileMatch [] qs d = case qs of
--    (Equation [] [] e:_)  -> pure e
--    (Equation [] cs e:qs) -> tagIf (getTag e) (foldr1 eAnd cs) e <$> compileMatch [] qs d
--compileMatch (u:us) qs d = 
--    foldrM run d (equationGroups qs)
--  where
--    run (ConHead, eqs) def = do
--        eqs' <- traverse fn (conGroups eqs)
--        case eqs' <> [Equation [sVar (getTag u) "$_"] [] def | eErr /= def] of
--            []                      -> pure def
--            clss@(Equation _ _ e:_) -> pure (tagMatch (getTag e) [u] clss)
--      where
--        fn (name, rs, t, eqs') = do
--            vars <- traverse (\r -> tagVar (getRepTag r) <$> supply) rs
--            expr <- compileMatch (vars <> us) eqs' def
--            pure (Equation [sCon t name (varName <$> vars)] [] expr)
--
--    run (VarHead, eqs) def = 
--        compileMatch us (fn <$> eqs) def
--      where
--        fn (Equation (Fix (RVar _ name):rs) c e) =
--            substitute name u <$> Equation rs c e 
--        fn eq = eq
--
--    varName (Fix (EVar _ name)) = name
--
--substitute :: Name -> SimpleExpr t -> SimpleExpr t -> SimpleExpr t
--substitute name subst = para $ \case
--    ELet t pat (_, e1) e2 -> tagLet t pat e1 e2'
--      where 
--        e2' | name `elem` free pat = fst e2
--            | otherwise            = snd e2
--
--    ELam t pat expr -> tagLam t pat expr'
--      where
--        expr' | name `elem` free pat = fst expr
--              | otherwise            = snd expr
--
--    EMatch t exs eqs ->
--        tagMatch t (snd <$> exs) (substEq <$> eqs)
--
--    expr -> snd <$> expr & \case
--        EVar t var -> tagVar t var
--        ELit t lit -> tagLit t lit
--        EApp t exs -> tagApp t exs
--
--  where
--    substEq 
--      :: Equation (SimpleRep t) (SimpleExpr t, SimpleExpr t) 
--      -> Equation (SimpleRep t) (SimpleExpr t)
--    substEq (Equation ps exs e) =
--        Equation ps (get <$> exs) (get e)
--          where
--            get | name `elem` unions (free <$> ps) = fst
--                | otherwise                        = snd
--
----desugar :: (MonadSupply Name m) => PatternExpr t -> m (RepExpr t)
----desugar = cata $ \case
----    EVar t var       -> pure (tagVar t var)
----    ELit t lit       -> pure (tagLit t lit)
----    EApp t exs       -> tagApp t <$> sequence exs
----    ELet t rep e1 e2 -> tagLet t rep <$> e1 <*> e2
----    ELam t rep ex    -> tagLam t rep <$> ex
----    EMatch t exs eqs -> do
----        resPair <- runWriterT (traverse desugarEquation eqs)
----        exs1 <- sequence exs
----        exs2 <- traverse desugar (snd resPair)
----        pure (tagMatch t (exs1 <> exs2) (fst resPair))
----
----desugarEquation :: (MonadSupply Name m) => Equation (Pattern t) (m (RepExpr t)) -> WriterT [PatternExpr t] m (RepEq t)
----desugarEquation (Equation ps exs e) =
----    Equation <$> traverse patternRep ps
----             <*> lift (sequence exs) 
----             <*> lift e 

patternVars :: Pattern t -> [(Name, t)]
patternVars = cata $ \case
    PVar t var    -> [(var, t)]
    PCon _ con rs -> concat rs
    PLit _ lit    -> []
    PAny _        -> []

--repVars :: Rep t -> [(Name, t)]
--repVars = cata $ \case
--    RVar t var    -> [(var, t)]
--    RCon _ con rs -> concat rs
--
--patternReps :: [Pattern t] -> ([Rep t], [PatternExpr t])
--patternReps = fmap concat . unzip . fmap patternRep
--
--patternRep :: Pattern t -> (Rep t, [PatternExpr t])
--patternRep pat = fromJust (evalSupply (runWriterT (toRep pat)) (nameSupply "$"))
--
--toRep :: Pattern t -> WriterT [PatternExpr t] (Supply Name) (Rep t)
--toRep =  cata alg where
--    alg pat = do
--        case pat of
--            PVar t var    -> pure (rVar t var)
--            PCon t con ps -> rCon t con <$> sequence ps 
--            PAny t        -> pure (rVar t "$_")
--            PLit t lit -> do
--                var <- supply
--                tell [tagEq (tagVar t var) (tagLit t lit)]
--                pure (rVar t var)
--
--data Head = ConHead | VarHead
--    deriving (Show, Eq, Ord)
--
--headType :: Equation (Rep t) a -> Head
--headType (Equation ps _ _) = 
--    case project <$> ps of
--        RVar{}:_ -> VarHead
--        _        -> ConHead
--
--equationGroups :: [SimpleEq t] -> [(Head, [SimpleEq t])]
--equationGroups = cata alg . fmap taggedEq 
--  where
--    alg :: Algebra (ListF (Head, SimpleEq t)) [(Head, [SimpleEq t])]
--    alg Nil =
--        []
--    alg (Cons (pt, eq) []) =
--        [(pt, [eq])]
--    alg (Cons (pt, eq) (group@(qt, eqs):gs))
--        | pt == qt  = (pt, eq:eqs):gs
--        | otherwise = (pure <$> taggedEq eq):group:gs
--
--    taggedEq eq = (headType eq, eq)
--
--conGroups :: [SimpleEq t] -> [(Name, [Rep t], t, [SimpleEq t])]
--conGroups =
--    concatMap conGroup
--      . groupSortOn (fst3 . fst)
--      . concatMap expanded
--  where
--    expanded (Equation (Fix (RCon t con rs):qs) c e) =
--        [((con, rs, t), Equation (rs <> qs) c e)]
--    expanded _ =
--        []
--    conGroup gs@(((con, rs, t), _):_) =
--        [(con, rs, t, snd <$> gs)]
--    conGroup [] =
--        []

specialized :: Name -> [t] -> [[Pattern t]] -> [[Pattern t]]
specialized name ts = concatMap rec where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ name' ps'
                | name' == name -> [ps' <> ps]
                | otherwise     -> []
            _ ->
                [(anyPat <$> ts) <> ps]

defaultMatrix :: [[Pattern t]] -> [[Pattern t]]
defaultMatrix = concatMap $ \(p:ps) ->
    case project p of
        PCon{} -> []
        PLit{} -> []
        _      -> [ps]

type ConstructorEnv = Env (Set Name)

constructorEnv :: [(Name, [Name])] -> ConstructorEnv
constructorEnv = Env.fromList . fmap (Set.fromList <$>)

useful :: (MonadReader ConstructorEnv m) => [[Pattern t]] -> [Pattern t] -> m Bool
useful [] _ = 
    -- Zero rows (0x0 matrix)
    pure True         
useful px@(ps:_) qs =
    case (qs, length ps) of
        -- One or more rows but no columns
        (_, 0) -> 
            pure False    

        ([], _) ->
            error "Implementation error (useful)"

        (Fix (PCon _ con rs):_, _) ->
            undefined
--            let special = specialized name (length rs)
--             in useful (special px) (head (special [qs]))
--
        (_:qs1, _) -> do
            undefined
--            cs <- headCons px
--            isComplete <- complete (fst <$> cs)
--            if isComplete
--                then cs & anyM (\con ->
--                    let special = uncurry specialized con
--                     in useful (special px) (head (special [qs])))
--                else useful (defaultMatrix px) qs1
  where
    complete [] = 
        pure False
    complete names@(name:_) = do
        defined <- ask
        let constructors = defined `Env.union` builtIn
        pure (Env.findWithDefaultEmpty name constructors == Set.fromList names)

    builtIn = constructorEnv
        [ ("$True",     ["$True", "$False"])
        , ("$False",    ["$True", "$False"])
        , ("$()",       ["$()"])
        , ("$Int",      [])
        , ("$Integer",  [])
        , ("$Float",    [])
        , ("$Char",     [])
        , ("$String",   []) ]

exhaustive :: (MonadReader ConstructorEnv m) => [[Pattern t]] -> m Bool
exhaustive []        = pure False
exhaustive px@(ps:_) = not <$> useful px (anyPat . getPatternTag <$> ps)
