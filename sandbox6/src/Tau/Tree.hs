{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
module Tau.Tree where

import Control.Arrow ((>>>))
import Control.Monad ((<=<))
import Control.Monad.Except
import Control.Monad.Extra (andM, anyM, (||^))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Supply
import Control.Monad.Writer
import Data.Either (fromRight)
import Data.Eq.Deriving
import Data.Fix (Fix(..))
import Data.Foldable (foldrM, foldlM)
import Data.Function ((&))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.List (nub, tails, partition, find, groupBy)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, fromJust)
import Data.Ord.Deriving
import Data.Tuple.Extra (both, first, second)
import Data.Void (Void)
import Tau.Env (Env)
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

ambiguityCheck
  :: ( MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => ProgExpr TInfo Void
  -> WriterT Name m (ProgExpr TInfo Void)
ambiguityCheck = cata $ \case

    EVar t var -> do
        classEnv <- askClassEnv
        let vs = filter (tIsVar . predicateType) (nodePredicates t)
        -- qs <- fromRight (error "impl") <$> reduce classEnv vs
        undefined

    EHole   t             -> pure (holeExpr t)
    ECon    t con es      -> conExpr t con <$> sequence es
    ELit    t prim        -> pure (litExpr t prim)
    EApp    t es          -> appExpr t <$> sequence es
    ELet    t bind e1 e2  -> letExpr t bind <$> e1 <*> e2
    EFix    t name e1 e2  -> fixExpr t name <$> e1 <*> e2
    ELam    t ps e        -> lamExpr t ps <$> e
    EIf     t e1 e2 e3    -> ifExpr t <$> e1 <*> e2 <*> e3
    EPat    t es cs       -> patExpr t <$> es <*> traverse sequence cs
    EFun    t cs          -> funExpr t <$> traverse sequence cs
    EOp1    t op a        -> op1Expr t op <$> a
    EOp2    t op a b      -> op2Expr t op <$> a <*> b
    ETuple  t es          -> tupleExpr t <$> sequence es
    EList   t es          -> listExpr t <$> sequence es
    ERow    t lab e r     -> rowExpr t lab <$> e <*> r
    ERecord t r           -> recordExpr t <$> r

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

data MonoClause t p a = MonoClause t [p] (Choice a)

type Stage1Expr t = Expr t t t t t t t t t Void Void [ProgPattern t Void]
    (MonoClause t (ProgPattern t Void)) (ProgBinding t Void)
    (MonoClause t [ProgPattern t Void])

s1ExprTag :: Stage1Expr t -> t
s1ExprTag = cata $ \case

    EVar    t _        -> t
    ECon    t _ _      -> t
    ELit    t _        -> t
    EApp    t _        -> t
    EFix    t _ _ _    -> t
    ELam    t _ _      -> t
    EIf     t _ _ _    -> t
    EPat    t _ _      -> t
    ELet    t _ _ _    -> t

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

instance (Typed t) => Typed (Stage1Expr t) where
    typeOf = typeOf . s1ExprTag

-------------------------------------------------------------------------------

-- S1. Desugaring

s1_translate :: ProgExpr TInfo Void -> Stage1Expr TInfo
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

translateAppExpr :: TInfo -> [Stage1Expr TInfo] -> Stage1Expr TInfo
translateAppExpr t es =
    foldr go
        (appExpr (remArgs (length es - 1) <$> s1ExprTag (head es)) replaceHoles)
        holes
  where
    go :: (Stage1Expr TInfo, Name) -> Stage1Expr TInfo -> Stage1Expr TInfo
    go (e, n) body = lamExpr
        (tArr (nodeType (s1ExprTag e)) <$> s1ExprTag body)
        [varPat (s1ExprTag e) n] body

    holes :: [(Stage1Expr TInfo, Name)]
    holes = zip (filter (hole . project) es) ["^" <> showt n | n <- nats]

    replaceHoles = fromJust (evalSupply (mapM f es) nats)
      where
        f e | hole (project e) = do
                n <- supply
                pure (varExpr (s1ExprTag e) ("^" <> showt n))
            | otherwise =
                pure e

    hole (EVar _ "^") = True
    hole _            = False

    remArgs :: Int -> Type -> Type
    remArgs 0 t = t
    remArgs n (Fix (TArr _ t2)) = remArgs (pred n) t2

translateFunExpr
  :: TInfo
  -> [MonoClause TInfo (ProgPattern TInfo Void) (Stage1Expr TInfo)]
  -> Stage1Expr TInfo
translateFunExpr t cs@(MonoClause _ ps (Choice _ e1):_) =
    lamExpr t (args varPat) (patExpr (s1ExprTag e1) e (toClause <$> cs))
--    lamExpr t (args varPat) (patExpr (TypeInfo [] (typeOf e1) []) e (toClause <$> cs))  -- ???
  where
    e = case args varExpr of
        [e] -> e
        es  -> conExpr (TypeInfo [] (tTuple (typeOf <$> es)) []) (tupleCon (length es)) es

    args con = [con (patternTag p) ("#" <> showt n) | (p, n) <- zip ps nats]

    toClause clause@(MonoClause t ps ds)
        | length ps < 2 = clause
        | otherwise     = MonoClause t [q] ds
      where
        q = conPat (TypeInfo [] (tTuple (typeOf <$> ps)) []) (tupleCon (length ps)) ps

nats :: [Int]
nats = enumFrom 0

-------------------------------------------------------------------------------

type Stage2Expr t = Expr t t t t t t t t Void Void Void Name
    (MonoClause t (Pattern t t t Void Void Void)) (ProgBinding t Void)
    (MonoClause t [Pattern t t t Void Void Void])

s2ExprTag :: Stage2Expr t -> t
s2ExprTag = cata $ \case

    EVar    t _        -> t
    ECon    t _ _      -> t
    ELit    t _        -> t
    EApp    t _        -> t
    EFix    t _ _ _    -> t
    ELam    t _ _      -> t
    EIf     t _ _ _    -> t
    EPat    t _ _      -> t

-------------------------------------------------------------------------------

-- S2. Simplification

s2_translate
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Stage1Expr TInfo
  -> m (Stage2Expr TInfo)
s2_translate = cata $ \case

    ELet t bind e1 e2 -> do
        a <- e1
        b <- e2
        translateLet t bind a b

    ELam t ps expr ->
        expr >>= translateLambda t ps

    EPat t expr clauses -> do
        e <- expr
        cs <- traverse sequence clauses
        translateMatchExpr t e cs

    ELit    t prim       -> pure (litExpr t prim)
    EVar    t var        -> pure (varExpr t var)
    ECon    t con exs    -> conExpr t con <$> sequence exs
    EFix    t name e1 e2 -> fixExpr t name <$> e1 <*> e2
    EApp    t es         -> appExpr t <$> sequence es
    EIf     t e1 e2 e3   -> ifExpr  t <$> e1 <*> e2 <*> e3

translateLet
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => TInfo
  -> Binding TInfo (ProgPattern TInfo Void)
  -> Stage2Expr TInfo
  -> Stage2Expr TInfo
  -> m (Stage2Expr TInfo)
translateLet t bind e1 e2 =
    case project <$> bind of
        BPat _ (PVar _ var) ->
            pure (fixExpr t var e1 e2)

        BPat _ pat -> do
            translateMatchExpr t e1 [MonoClause t [embed pat] (Choice [] e2)]

        BFun t f ps -> do
            e <- translateLambda t (embed <$> ps) e1
            translateMatchExpr t e [MonoClause t [varPat t f] (Choice [] e2)]

translateLambda
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => TInfo
  -> [ProgPattern TInfo Void]
  -> Stage2Expr TInfo
  -> m (Stage2Expr TInfo)
translateLambda t pats expr =
    case project <$> pats of
        [PVar _ var] -> pure (lamExpr t var expr)
        _            -> fst <$> foldrM fn (expr, s2ExprTag expr) pats
  where
    fn pat (expr, t) = do
        var <- freshName
        let ti = TypeInfo [] (nodeType (patternTag pat) `tArr` nodeType t) []
        e <- translateMatchExpr t (varExpr (patternTag pat) var)
                                  [MonoClause t [pat] (Choice [] expr)]
        pure (lamExpr ti var e, ti)

translateMatchExpr
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => TInfo
  -> Stage2Expr TInfo
  -> [MonoClause TInfo (ProgPattern TInfo Void) (Stage2Expr TInfo)]
  -> m (Stage2Expr TInfo)
translateMatchExpr t expr clauses =
    patExpr t expr . concat <$> traverse expandClausePatterns clauses
  where
    expandClausePatterns (MonoClause t ps (Choice es e)) = do
        (qs, ds) <- runWriterT (traverse expandPatterns1 ps)
        pure (expandPatterns2 [MonoClause t qs (Choice (es <> ds) e)])

    expandPatterns1 = cata $ \case

        PLit t prim -> do
            var <- freshName
            tell [ appExpr (TypeInfo [] tBool [])
                     [ varExpr (TypeInfo [] (nodeType t `tArr` nodeType t `tArr` tBool) []) "(==)"
                     , varExpr (TypeInfo [] (nodeType t) []) var
                     , litExpr t prim ] ]
            pure (varPat t var)

        PRow t lab p q -> do
            a <- p
            b <- q
            pure (conPat t ("{" <> lab <> "}") [a, b])

        PRecord t r -> do
            a <- r
            pure (conPat t "#" [a])

        PTuple  t ps      -> conPat t (tupleCon (length ps)) <$> sequence ps
        PList   t ps      -> foldr (listPatCons t) (conPat t "[]" []) <$> sequence ps
        PAny    t         -> varPat t <$> freshName

        PVar    t var     -> pure (varPat t var)
        PCon    t con ps  -> conPat t con <$> sequence ps
        PAs     t name a  -> asPat t name <$> a
        POr     t a b     -> orPat t <$> a <*> b

    expandPatterns2 = concatMap $ \(MonoClause t ps g) ->
        [MonoClause t qs g | qs <- traverse fn ps]
      where
        fn = cata $ \case

            PVar t var       -> pure (varPat t var)
            PCon t con ps    -> conPat t con <$> sequence ps
            PAs  t name a    -> asPat t name <$> a
            POr  _ a b       -> a <> b

translateLiteral :: Stage2Expr TInfo -> Stage2Expr TInfo
translateLiteral = cata $ \case

    ELit t (TInt n) -> appExpr t
        [ varExpr (t{ nodeType = tArr tInteger (nodeType t) }) "fromInteger"
        , litExpr (TypeInfo [] tInteger []) (TInteger (fromIntegral n)) ]

    ELit t (TInteger n) -> appExpr t
        [ varExpr (t{ nodeType = tArr tInteger (nodeType t) }) "fromInteger"
        , litExpr (TypeInfo [] tInteger []) (TInteger n) ]

    ELit t (TFloat r) -> appExpr t
        [ varExpr (t{ nodeType = tArr tDouble (nodeType t) }) "fromDouble"
        , litExpr (TypeInfo [] tDouble []) (TDouble (fromRational (toRational r))) ]

    ELit t (TDouble r) -> appExpr t
        [ varExpr (t{ nodeType = tArr tDouble (nodeType t) }) "fromDouble"
        , litExpr (TypeInfo [] tDouble []) (TDouble r) ]

    e -> embed e

freshName
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => m Name
freshName = ("$e" <>) . showt <$> supply

-------------------------------------------------------------------------------

type Stage3Expr t = Expr t t t t t t t t Void Void Void Name
    (MonoClause t (Pattern t t t Void Void Void)) (ProgBinding t Void)
    (MonoClause t [Pattern t t t Void Void Void])

-------------------------------------------------------------------------------

-- S3. Typeclass expansion

s3_translate
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Stage2Expr TInfo
  -> StateT (Env [(Name, Name)]) m (Stage3Expr Type)
s3_translate expr = do
    e <- walk expr
    s <- getAndReset
    insertArgsExpr e s
  where
    walk
      :: ( MonadSupply Int m
         , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
      => Stage2Expr TInfo
      -> StateT (Env [(Name, Name)]) m (Stage3Expr Type)
    walk = cata $ \case

        EPat t expr cs -> do
            e <- expr
            s <- getAndReset
            patExpr (nodeType t) <$> insertArgsExpr e s <*> (translateClauses <$$> traverse sequence cs)

        EFix t var expr1 expr2 -> do
            e <- expr1
            s <- getAndReset
            fixExpr (nodeType t) var <$> insertArgsExpr e s <*> expr2

        EVar t var -> do
            let (vs, ts) = partition (tIsVar . predicateType) (nodePredicates t)

            classEnv <- askClassEnv
            fromType <- traverse (reduceSet classEnv)
                (foldr (\(InClass n t) -> Map.insertWith (<>) t [n]) mempty ts)

            let ps = Map.foldrWithKey (\k ns ps -> [InClass n k | n <- ns] <> ps) [] fromType
            e1 <- foldlM applyNonVarPredicates (varExpr (nodeType t) var) (tails ps)

            qs <- fromRight (error "Implementation error") <$> reduce classEnv vs
            foldlM applyVarPredicates e1 (tails qs)

        ELit   t prim      -> pure (litExpr (nodeType t) prim)
        ECon   t con es    -> conExpr (nodeType t) con <$> sequence es
        EApp   t es        -> appExpr (nodeType t) <$> sequence es
        ELam   t name e    -> lamExpr (nodeType t) name <$> e
        EIf    t e1 e2 e3  -> ifExpr  (nodeType t) <$> e1 <*> e2 <*> e3

    translatePatterns = cata $ \case
        PVar   t var       -> varPat  (nodeType t) var
        PCon   t con ps    -> conPat  (nodeType t) con ps
        PAs    t as p      -> asPat   (nodeType t) as p

    translateClauses = \case
        MonoClause t ps g ->
            MonoClause (nodeType t) (translatePatterns <$> ps) g

dictTVar
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Name
  -> TypeF k i a
  -> StateT (Env [(Name, Name)]) m Name
dictTVar name (TVar _ var) = do
    info <- get
    classEnv <- askClassEnv
    maybe fresh pure (lookupVar info classEnv)
  where
    fresh = do
        dv <- ("$dict" <>) . showt <$> supply
        modify (Env.alter (\vs -> Just $ (name, dv):fromMaybe [] vs) var)
        pure dv

    lookupVar info classEnv = do
        varEnv <- Env.lookup var info
        snd <$> find (elem name . fst) (first (super1 classEnv) <$> varEnv)

applyVarPredicates
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => Stage3Expr Type
  -> [Predicate]
  -> StateT (Env [(Name, Name)]) m (Stage3Expr Type)
applyVarPredicates expr [] = pure expr
applyVarPredicates expr (InClass name ty:ps) = do
    tv <- dictTVar name (project ty)
    case project expr of
        EVar t var -> do
            all <- baz
            if var `elem` (fst <$> all)
                then pure (appExpr tempT -- (workingExprTag2 expr)
                    [ varExpr tempT "@(#)get_field"
                    , litExpr tSymbol (TSymbol var)
                    , varExpr tempT tv ])
                else pure (appExpr tempT -- zz1
                    [ expr -- setWorkingExprTag2 (yy (InClass name ty) zz1) expr
                    , varExpr tempT tv ])
        _ ->
            pure (appExpr tempT [expr, varExpr tempT tv ])
  where
    baz = do
        env <- askClassEnv
        fromRight (error ("No class " <> show name))   -- TODO
            <$> runExceptT (lookupAllMethods name env)

tempT = tVar kTyp "TODO"

lookupAllMethods
  :: (MonadSupply Int m, MonadError Error m)
  => Name
  -> ClassEnv
  -> m [(Name, Type)]
lookupAllMethods name env = do
    (ClassInfo{..}, _) <- liftMaybe (NoSuchClass name) (Env.lookup name env)
    super <- concat <$$> forM classPredicates $ \(InClass name _) ->
        lookupAllMethods name env
    pure (super <> classMethods)

applyNonVarPredicates
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => x
  -> [Predicate]
  -> StateT (Env [(Name, Name)]) m (Stage3Expr Type)
applyNonVarPredicates = undefined

insertArgsExpr
  :: ( MonadSupply Int m
     , MonadReader (ClassEnv, TypeEnv, KindEnv, ConstructorEnv) m )
  => x
  -> Env [(Name, Name)]
  -> StateT (Env [(Name, Name)]) m (Stage3Expr Type)
insertArgsExpr = undefined
