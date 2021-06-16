{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StrictData           #-}
module Tau.Compiler.Patterns where

import Control.Monad.Extra
import Control.Monad.Reader
import Data.Function ((&))
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.Tuple.Extra (first, second)
import Tau.Lang
import Tau.Prog
import Tau.Tooling
import Tau.Type
import qualified Data.Map.Strict as Map
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

xx1 :: (Show t, RowType t) => ProgPattern t -> ProgPattern t
xx1 = cata $ \case
    PVar    t var        -> varPat t var
    PCon    t con ps     -> conPat t con ps
    PLit    t prim       -> litPat t prim
    PAs     t as p       -> asPat t as p
    POr     t p q        -> orPat t p q
    PAny    t            -> anyPat t
    PTuple  t ps         -> tuplePat t ps
    PList   t ps         -> listPat t ps
    p@PRow{}             -> foldRow (embed p)
    PAnn    t p          -> annPat t p

xx2 :: (Show t, RowType t) => ProgPattern t -> ProgPattern t
xx2 = cata $ \case
    PVar    t var        -> varPat t var
    PCon    t con ps     -> conPat t con ps
    PLit    t prim       -> litPat t prim
    PAs     t as p       -> asPat t as p
    POr     t p q        -> orPat t p q
    PAny    t            -> anyPat t
    PTuple  t ps         -> tuplePat t ps
    PList   t ps         -> listPat t ps
    PRow    t lab p q    -> conPat t ("{" <> lab <> "}") [p, q]
    PAnn    t p          -> annPat t p

useful pss ps = useful1 (xx2 . xx1 <$$> pss) (xx2 . xx1 <$> ps)

useful1 :: (Show t, RowType t, MonadReader ConstructorEnv m) => [[ProgPattern t]] -> [ProgPattern t] -> m Bool
useful1 [] _ = pure True     -- Zero rows (0x0 matrix)
useful1 (p1:_) qs 
    | null p1 = pure False  -- One or more rows but no columns
    | null qs = error "Implementation error (useful1)"
useful1 pss (q:qs) = do
    traceShowM pss
    case groupPatterns q of
        ConGroup con rs  ->
            let special = specialized con (patternTag <$> rs)
             in useful1 (special pss) (head (special [q:qs]))
        WildcardPattern -> do
            let cs = headCons pss
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) -> do
                    let special = specialized con (patternTag <$> rs)
                     in useful1 (special pss) (head (special [q:qs]))) 
                else 
                    useful1 (defaultMatrix pss) qs
        OrPattern a b -> 
            useful1 pss (a:qs) ||^ useful1 pss (b:qs)
  where
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

data PatternGroup t
    = ConGroup Name [ProgPattern t] 
    | OrPattern (ProgPattern t) (ProgPattern t)
    | WildcardPattern
    deriving (Show, Eq)

groupPatterns :: (Show t, RowType t) => ProgPattern t -> PatternGroup t
groupPatterns = project >>> \case
    PCon   _ con rs  -> ConGroup con rs
    PTuple t elems   -> groupPatterns (foldTuple t elems)
    PList  t elems   -> groupPatterns (foldList t elems)
    PLit   t lit     -> groupPatterns (conPat t (prim lit) [])
    PAs    _ _ a     -> groupPatterns a
    POr    _ a b     -> OrPattern a b
    _                -> WildcardPattern

specialized :: (Show t, RowType t) => Name -> [t] -> [[ProgPattern t]] -> [[ProgPattern t]]
specialized name ts = (rec =<<)
  where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ con rs
                | con == name -> [rs <> ps]
                | otherwise   -> []

            PLit   t lit      -> rec (conPat t (prim lit) []:ps)
            PTuple t elems    -> rec (foldTuple t elems:ps)
            PList  t elems    -> rec (foldList t elems:ps)
            PAs    _ _ q      -> rec (q:ps)
            POr    _ p1 p2    -> rec (p1:ps) <> rec (p2:ps)
            _                 -> [(anyPat <$> ts) <> ps]

defaultMatrix :: [[ProgPattern t]] -> [[ProgPattern t]]
defaultMatrix = (fun =<<)
  where
    fun :: [ProgPattern t] -> [[ProgPattern t]]
    fun (p:ps) =
        case project p of
            PCon{}     -> []
            PTuple{}   -> []
            PList{}    -> []
            PRow{}     -> []
            PLit{}     -> []
            PAnn _ p   -> fun (p:ps)
            PAs  _ _ q -> fun (q:ps)
            POr  _ q r -> fun (q:ps) <> fun (r:ps)
            _          -> [ps]

foldTuple :: t -> [ProgPattern t] -> ProgPattern t
foldTuple t elems = conPat t (tupleCon (length elems)) elems

foldList :: t -> [ProgPattern t] -> ProgPattern t
foldList t = foldr (listPatCons t) (conPat t "[]" [])

class RowType t where
    rowType :: Name -> t -> t -> t

instance RowType () where
    rowType _ _ _ = ()

instance (RowType t) => RowType (Maybe t) where
    rowType lab a b = rowType lab <$> a <*> b

instance (RowType t) => RowType (TypeInfoT [e] t) where
    rowType lab a b = TypeInfo [] (rowType lab (nodeType a) (nodeType b)) []

instance RowType Type where
    rowType = tRow 

foldRow :: (Show t, RowType t) => ProgPattern t -> ProgPattern t
foldRow r = fromMap final mapRep
  where
    mapRep = foldr (uncurry (Map.insertWith (<>))) mempty fields

    fromMap :: (RowType t) => ProgPattern t -> Map Name [ProgPattern t] -> ProgPattern t
    fromMap p ps = 
        fst (Map.foldrWithKey (flip . foldr . fn) (p, patternTag p) ps)
      where 
        fn name p (q, t0) = 
            let t1 = rowType name (patternTag p) t0
                --label = "{" <> name <> "}"
             --in (conPat t1 label [p, q], t1)
             in (rowPat t1 name p q, t1)

    fields = flip para r $ \case
        PRow _ label p rest -> (label, [fst p]):snd rest
        _                   -> []

    final = flip cata r $ \case
        PRow _ _ _ r        -> r
        p                   -> embed p

headCons :: (Show t, RowType t) => [[ProgPattern t]] -> [(Name, [ProgPattern t])]
headCons = (>>= fun) 
  where
    fun :: (Show t, RowType t) => [ProgPattern t] -> [(Name, [ProgPattern t])]
    fun [] = error "Implementation error (headCons)"
    fun (p:ps) = 
        case project p of
            PLit   _ p               -> [(prim p, [])]
            PCon   _ name rs         -> [(name, rs)]
            PTuple t elems           -> fun (foldTuple t elems:ps)
            PList  t elems           -> fun (foldList t elems:ps)
            PAs    _ _ q             -> fun (q:ps)
            POr    _ a b             -> fun (a:ps) <> fun (b:ps)
            _                        -> []

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

exhaustive :: (Show t, RowType t, MonadReader ConstructorEnv m) => [[ProgPattern t]] -> m Bool
exhaustive []         = pure False
exhaustive pss@(ps:_) = not <$> useful pss (anyPat . patternTag <$> ps)

-- | Determine if all patterns in the expression are exhaustive.
--
checkExhaustive :: (Show t, Eq t, RowType t, MonadReader ConstructorEnv m) => ProgExpr t -> m Bool
checkExhaustive = para $ \case

    EPat _ a clauses -> snd a &&^ clausesAreExhaustive (fst <$$> clauses)
    EFun _ clauses   -> clausesAreExhaustive (fst <$$> clauses)

    expr -> snd <$> expr & \case
        ECon   _ _ exprs             -> andM exprs
        EApp   _ exprs               -> andM exprs
        ELet   _ (BLet _ p) e1 e2    -> exhaustive [[p]] &&^ e1 &&^ e2
        ELet   _ (BFun _ _ ps) e1 e2 -> exhaustive [ps] &&^ e1 &&^ e2
        EFix   _ _ e1 e2             -> e1 &&^ e2
        ELam   _ ps e1               -> exhaustive [ps] &&^ e1
        EIf    _ cond tr fl          -> cond &&^ tr &&^ fl
        EOp1   _ _ a                 -> a
        EOp2   _ _ a b               -> a &&^ b
        ETuple _ elems               -> andM elems
        EList  _ elems               -> andM elems
        ERow   _ _ e1 e2             -> e1 &&^ e2
        EAnn   _ e                   -> e
        _                            -> pure True

clausesAreExhaustive :: (Show t, Eq t, RowType t, MonadReader ConstructorEnv m) => [Clause t (ProgPattern t) (ProgExpr t)] -> m Bool
clausesAreExhaustive = exhaustive . fmap toMatrix
  where
    toMatrix (Clause _ p guards)
        | null guards           = [p]
        | any isCatchAll guards = [p]
    toMatrix _ = 
        []

    isCatchAll (Guard [ ] _)            = True
    isCatchAll (Guard [b] _) | isTrue b = True
    isCatchAll _                        = False

    isTrue :: ProgExpr t -> Bool
    isTrue = project >>> \case
        ELit _ (TBool True) -> True
        _                   -> False
