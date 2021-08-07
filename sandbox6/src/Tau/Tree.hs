{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Tree where

import Control.Arrow ((>>>))
import Control.Monad ((<=<))
import Control.Monad.Extra (andM, anyM, (||^))
import Control.Monad.Reader
import Data.Eq.Deriving
import Data.Function ((&))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.Map.Strict (Map)
import Data.Ord.Deriving
import Data.Tuple.Extra (both)
import Data.Void (Void)
import Tau.Misc
import Tau.Util
import Text.Show.Deriving
import TextShow (showt)
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

-------------------------------------------------------------------------------
-- Preflight
-------------------------------------------------------------------------------

type TInfo = TypeInfo [Error]

exhaustivePatternsCheck :: (MonadReader ConstructorEnv m) => ProgExpr TInfo Void -> m (ProgExpr TInfo Void)
exhaustivePatternsCheck = para $ \case

    EPat t expr clauses ->
        patExpr <$> check clausesAreExhaustive (patToList <$> (fst <$$> clauses)) t
                <*> snd expr
                <*> traverse sequence (snd <$$> clauses)

    EFun t clauses ->
        funExpr <$> check clausesAreExhaustive (fst <$$> clauses) t
                <*> traverse sequence (snd <$$> clauses)

    expr -> snd <$> expr & \case

        ELet t bind@(BPat _ p) e1 e2 ->
            letExpr <$> check exhaustive [[p]] t
                    <*> pure bind
                    <*> e1
                    <*> e2

        ELet t bind@(BFun _ _ ps) e1 e2 ->
            letExpr <$> check andM [exhaustive [[p]] | p <- ps] t
                    <*> pure bind
                    <*> e1
                    <*> e2

        ELam t ps e ->
            lamExpr <$> check andM [exhaustive [[p]] | p <- ps] t
                    <*> pure ps
                    <*> e

        EVar    t var         -> pure (varExpr t var)
        EHole   t             -> pure (holeExpr t)
        ECon    t con es      -> conExpr t con <$> sequence es
        ELit    t prim        -> pure (litExpr t prim)
        EApp    t es          -> appExpr t <$> sequence es
        EFix    t name e1 e2  -> fixExpr t name <$> e1 <*> e2
        EIf     t e1 e2 e3    -> ifExpr t <$> e1 <*> e2 <*> e3
        EOp1    t op a        -> op1Expr t op <$> a
        EOp2    t op a b      -> op2Expr t op <$> a <*> b
        ETuple  t es          -> tupleExpr t <$> sequence es
        EList   t es          -> listExpr t <$> sequence es
        ERow    t lab e r     -> rowExpr t lab <$> e <*> r
        ERecord t r           -> recordExpr t <$> r

  where
    check f as ti = do
        exhaustive <- f as
        pure (addErrors [NonExhaustivePatterns | not exhaustive] ti)

    patToList (Clause t p a) = Clause t [p] a

exhaustive :: (MonadReader ConstructorEnv m) => [[ProgPattern TInfo u]] -> m Bool
exhaustive []         = pure False
exhaustive pss@(ps:_) = not <$> useful pss (anyPat . patternTag <$> ps)

clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [Clause t [ProgPattern TInfo u] (ProgExpr t u)] -> m Bool
clausesAreExhaustive = exhaustive . fmap toMatrix
  where
    toMatrix (Clause _ ps choices)
        | null choices                   = ps
        | any isCatchAll choices         = ps
    toMatrix _                           = []

    isCatchAll (Choice [ ] _)            = True
    isCatchAll (Choice [b] _) | isTrue b = True
    isCatchAll _                         = False

    isTrue = project >>> \case
        ELit _ (TBool True)             -> True
        _                               -> False

data PatternGroup t u
    = ConGroup Name [ProgPattern t u]
    | OrPattern (ProgPattern t u) (ProgPattern t u)
    | WildcardPattern

useful :: (MonadReader ConstructorEnv m) => [[ProgPattern TInfo u]] -> [ProgPattern TInfo u] -> m Bool
useful pss ps = step3 (step2 . step1 <$$> pss) (step2 . step1 <$> ps)
  where
    step1 = cata $ \case
        p@PRow{}       -> foldRow (embed p)
        p              -> embed p

    step2 = cata $ \case
        PRow t lab p q -> tuplePat t [p, q]
        p              -> embed p

    step3 [] _ = pure True      -- Zero rows (0x0 matrix)
    step3 (p1:_) qs
        | null p1 = pure False  -- One or more rows but no columns
        | null qs = error "Implementation error (step3)"

    step3 pss (q:qs) =
        case groupPatterns q of
            ConGroup con rs  ->
                let special = specialized con (patternTag <$> rs)
                 in step3 (special pss) (head (special [q:qs]))
            WildcardPattern -> do
                let cs = headCons pss
                isComplete <- complete (fst <$> cs)
                if isComplete
                    then cs & anyM (\(con, rs) -> do
                        let special = specialized con (patternTag <$> rs)
                         in step3 (special pss) (head (special [q:qs])))
                    else
                        step3 (defaultMatrix pss) qs
            OrPattern a b ->
                step3 pss (a:qs) ||^ step3 pss (b:qs)

    complete :: (MonadReader ConstructorEnv m) => [Name] -> m Bool
    complete [] = pure False
    complete names@(name:_) = do
        defined <- ask
        pure (lookupCon (defined `Env.union` builtIn) name == Set.fromList names)

    lookupCon :: Env.Env (Set.Set Name, Int) -> Name -> Set.Set Name
    lookupCon constructors con
        | isTupleCon con || isRowCon con = Set.singleton con
        | otherwise = maybe mempty fst (Env.lookup con constructors)

    builtIn = constructorEnv
        [ ("#True",     ( ["#True", "#False"], 0 ))
        , ("#False",    ( ["#True", "#False"], 0 ))
        , ("#()",       ( ["#()"], 0 ))
        , ("#Int",      ( [], 1 ))
        , ("#Integer",  ( [], 1 ))
        , ("#Float",    ( [], 1 ))
        , ("#Char",     ( [], 1 ))
        , ("#String",   ( [], 1 ))
        , ("#",         ( ["#"], 1 ))
        , ("[]",        ( ["[]", "(::)"], 0 ))
        , ("(::)",      ( ["[]", "(::)"], 2 ))
        , ("Zero",      ( ["Zero", "Succ"], 0 ))
        , ("Succ",      ( ["Zero", "Succ"], 1 ))
        ]

specialized :: Name -> [TInfo] -> [[ProgPattern TInfo u]] -> [[ProgPattern TInfo u]]
specialized name ts = (rec =<<)
  where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ con rs
                | con == name -> [rs <> ps]
                | otherwise   -> []

            PLit    t lit     -> rec (conPat t (prim lit) []:ps)
            PTuple  t elems   -> rec (foldTuple t elems:ps)
            PList   t elems   -> rec (foldList t elems:ps)
            PRecord t row     -> rec (conPat t "#" [row]:ps)
            PAs     _ _ q     -> rec (q:ps)
            POr     _ p1 p2   -> rec (p1:ps) <> rec (p2:ps)
            _                 -> [(anyPat <$> ts) <> ps]

defaultMatrix :: [[ProgPattern TInfo u]] -> [[ProgPattern TInfo u]]
defaultMatrix = (fun =<<)
  where
    fun :: [ProgPattern TInfo u] -> [[ProgPattern TInfo u]]
    fun (p:ps) =
        case project p of
            PCon{}            -> []
            PTuple{}          -> []
            PList{}           -> []
            PRow{}            -> []
            PRecord{}         -> []
            PLit{}            -> []
            PAnn _ p          -> fun (p:ps)
            PAs  _ _ q        -> fun (q:ps)
            POr  _ q r        -> fun (q:ps) <> fun (r:ps)
            _                 -> [ps]

isTupleCon :: Name -> Bool
isTupleCon con = Just True == (allCommas <$> stripped con)
  where
    allCommas = Text.all (== ',')
    stripped  = Text.stripSuffix ")" <=< Text.stripPrefix "("

isRowCon :: Name -> Bool
isRowCon con = ("{", "}") == fstLst con
  where
    fstLst ""  = ("", "")
    fstLst con = both Text.singleton (Text.head con, Text.last con)

foldList :: TInfo -> [ProgPattern TInfo u] -> ProgPattern TInfo u
foldList t = foldr (listPatCons t) (conPat t "[]" [])

foldTuple :: TInfo -> [ProgPattern TInfo u] -> ProgPattern TInfo u
foldTuple t elems = conPat t (tupleCon (length elems)) elems

foldRow :: ProgPattern TInfo u -> ProgPattern TInfo u
foldRow r = fromMap final mapRep
  where
    mapRep = foldr (uncurry (Map.insertWith (<>))) mempty fields

    fromMap :: ProgPattern TInfo u -> Map Name [ProgPattern TInfo u] -> ProgPattern TInfo u
    fromMap p ps =
        fst (Map.foldrWithKey (flip . foldr . fn) (p, patternTag p) ps)
      where
        fn name p (q, t0) =
            let t1 = TypeInfo [] (tRow name (nodeType (patternTag p)) (nodeType t0)) []
             in (rowPat t1 name p q, t1)

    fields = flip para r $ \case
        PRow _ label p rest   -> (label, [fst p]):snd rest
        _                     -> []

    final = flip cata r $ \case
        PRow _ _ _ r          -> r
        p                     -> embed p

groupPatterns :: ProgPattern TInfo u -> PatternGroup TInfo u
groupPatterns = project >>> \case
    PCon    _ con rs          -> ConGroup con rs
    PTuple  t elems           -> groupPatterns (foldTuple t elems)
    PList   t elems           -> groupPatterns (foldList t elems)
    PRecord t row             -> groupPatterns (conPat t "#" [row])
    PLit    t lit             -> groupPatterns (conPat t (prim lit) [])
    PAs     _ _ a             -> groupPatterns a
    POr     _ a b             -> OrPattern a b
    _                         -> WildcardPattern

headCons :: [[ProgPattern TInfo u]] -> [(Name, [ProgPattern TInfo u])]
headCons = (>>= fun)
  where
    fun :: [ProgPattern TInfo u] -> [(Name, [ProgPattern TInfo u])]
    fun [] = error "Implementation error (headCons)"
    fun (p:ps) =
        case project p of
            PLit    _ p       -> [(prim p, [])]
            PCon    _ name rs -> [(name, rs)]
            PTuple  t elems   -> fun (foldTuple t elems:ps)
            PList   t elems   -> fun (foldList t elems:ps)
            PRecord t row     -> fun (conPat t "#" [row]:ps)
            PAs     _ _ q     -> fun (q:ps)
            POr     _ a b     -> fun (a:ps) <> fun (b:ps)
            _                 -> []

prim :: Prim -> Name
prim (TBool True)  = "#True"
prim (TBool False) = "#False"
prim TUnit         = "#()"
prim TInt{}        = "#Int"
prim TInteger{}    = "#Integer"
prim TFloat{}      = "#Float"
prim TDouble{}     = "#Double"
prim TChar{}       = "#Char"
prim TString{}     = "#String"

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

data MonoClause t p a = MonoClause t [p] (Choice a) 

type S1Expr t = Expr t t t t t t t t t t t t t t t t Void [ProgPattern t Void]
    (MonoClause t (ProgPattern t Void)) (ProgBinding t Void)
    (MonoClause t [ProgPattern t Void])

-------------------------------------------------------------------------------

deriving instance (Show t, Show p, Show a) => 
    Show (MonoClause t p a)

deriving instance (Eq t, Eq p, Eq a) => 
    Eq (MonoClause t p a)

deriving instance (Ord t, Ord p, Ord a) => 
    Ord (MonoClause t p a)

deriving instance Functor     (MonoClause t p)
deriving instance Foldable    (MonoClause t p)
deriving instance Traversable (MonoClause t p)

deriveShow1 ''MonoClause
deriveEq1   ''MonoClause
deriveOrd1  ''MonoClause

-- deriving instance (Show t) => Show (DesugaredPattern t)
-- deriving instance (Eq   t) => Eq   (DesugaredPattern t)

-------------------------------------------------------------------------------

-- S1. Desugaring

s1_translate :: ProgExpr TInfo Void -> S1Expr TInfo
s1_translate = cata $ \case

    -- Translate tuples, lists, records, and row expressions
    ETuple  t es                -> conExpr t (tupleCon (length es)) es
    EList   t es                -> foldr (listExprCons t) (conExpr t "[]" []) es
    ERow    t lab e r           -> conExpr t ("{" <> lab <> "}") [e, r]
    ERecord t r                 -> conExpr t "#" [r]

    -- Translate operators to prefix form
    EOp1    t op a              -> appExpr t [prefixOp1 op, a]
    EOp2    t op a b            -> translateAppExpr t [prefixOp2 op, a, b]

    -- Expand pattern clause guards and eliminate fun expressions
    EPat    t e cs              -> patExpr t e (expandClause . patToList =<< cs)
    EFun    t cs                -> translateFunExpr t (expandClause =<< cs)

    -- Remove holes in function application expressions
    EApp    t es                -> translateAppExpr t es
    EHole   t                   -> varExpr t "^" 

    -- Other expressions do not change, except sub-expressions
    EVar    t var               -> varExpr t var
    ECon    t con es            -> conExpr t con es
    ELit    t prim              -> litExpr t prim
    EFix    t name e1 e2        -> fixExpr t name e1 e2
    ELam    t ps e              -> lamExpr t ps e
    ELet    t bind e1 e2        -> letExpr t bind e1 e2
    EIf     t e1 e2 e3          -> ifExpr  t e1 e2 e3
  where
    prefixOp1 (ONeg t)    = varExpr t "negate"
    prefixOp1 (ONot t)    = varExpr t "not"
    prefixOp2 (OField t)  = varExpr t "@(#)get_field"
    prefixOp2 op          = varExpr (op2Tag op) ("(" <> op2Symbol op <> ")")

    patToList (Clause t p a)      = Clause t [p] a
    expandClause (Clause t ps gs) = [MonoClause t ps g | g <- gs]

-- TODO
translateAppExpr :: TInfo -> [S1Expr TInfo] -> S1Expr TInfo
translateAppExpr t es = appExpr t es

--translateFunExpr :: TInfo -> [MonoClause TInfo (ProgPattern TInfo Void) (S1Expr TInfo)] -> S1Expr TInfo
translateFunExpr t cs@(MonoClause _ ps _:_) =
    lamExpr t (xxx varPat) (patExpr (TypeInfo [] (tVar kTyp "TODO") []) e cs) -- (gork <$> cs))
  where
    e = case xxx varExpr of
        [e] -> e
        es  -> conExpr (TypeInfo [] (tVar kTyp "TODO") []) (tupleCon (length es)) es

    xxx con = [con (patternTag p) ("#" <> showt n) | (p, n) <- zip ps ([0..] :: [Int])]

--    gork (MonoClause t ps ds) = MonoClause t [r] ds
--      where
--        r = case ps of
--                p -> MonoClause t p ds
----            _   -> MonoClause t [q] ds

--        q = conPat (TypeInfo [] (tVar kTyp "TODO") []) (tupleCon (length ps)) ps

