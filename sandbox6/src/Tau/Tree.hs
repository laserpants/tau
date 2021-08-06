{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
module Tau.Tree where

import Control.Arrow ((>>>))
import Control.Monad ((<=<))
import Control.Monad.Extra (andM, anyM, (||^))
import Control.Monad.Reader
import Data.Function ((&))
import Data.Functor.Foldable (cata, para, project, embed)
import Data.Tuple.Extra (both)
import Data.Void (Void)
import Tau.Misc
import Tau.Util
import qualified Data.Set.Monad as Set
import qualified Data.Text as Text
import qualified Tau.Env as Env

-------------------------------------------------------------------------------
-- Preflight
-------------------------------------------------------------------------------

exhaustivePatternsCheck
  :: (MonadReader ConstructorEnv m)
  => ProgExpr (TypeInfo [Error]) Void
  -> m (ProgExpr (TypeInfo [Error]) Void)
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

  where
    check f as ti = do
        exhaustive <- f as
        pure (addErrors [NonExhaustivePatterns | not exhaustive] ti)

    patToList (Clause t p a) = Clause t [p] a

exhaustive :: (MonadReader ConstructorEnv m) => [[ProgPattern t u]] -> m Bool
exhaustive []         = pure False
exhaustive pss@(ps:_) = not <$> useful pss (anyPat . patternTag <$> ps)

clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [Clause t [ProgPattern t u] (ProgExpr t u)] -> m Bool
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

useful :: (MonadReader ConstructorEnv m) => [[ProgPattern t u]] -> [ProgPattern t u] -> m Bool
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

--    complete :: (MonadReader ConstructorEnv m) => [Name] -> m Bool
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

specialized :: Name -> [t] -> [[ProgPattern t u]] -> [[ProgPattern t u]]
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

defaultMatrix :: [[ProgPattern t u]] -> [[ProgPattern t u]]
defaultMatrix = (fun =<<)
  where
    fun :: [ProgPattern t u] -> [[ProgPattern t u]]
    fun (p:ps) =
        case project p of
            PCon{}            -> []
            PTuple{}          -> []
            PList{}           -> []
            PRow{}            -> []
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

foldList :: t -> [ProgPattern t u] -> ProgPattern t u
foldList t = foldr (listPatCons t) (conPat t "[]" [])

foldTuple :: t -> [ProgPattern t u] -> ProgPattern t u
foldTuple t elems = conPat t (tupleCon (length elems)) elems

foldRow :: ProgPattern t u -> ProgPattern t u
foldRow = undefined

groupPatterns :: ProgPattern t u -> PatternGroup t u
groupPatterns = project >>> \case
    PCon   _ con rs  -> ConGroup con rs
    PTuple t elems   -> groupPatterns (foldTuple t elems)
    PList  t elems   -> groupPatterns (foldList t elems)
    PLit   t lit     -> groupPatterns (conPat t (prim lit) [])
    PAs    _ _ a     -> groupPatterns a
    POr    _ a b     -> OrPattern a b
    _                -> WildcardPattern

headCons :: [[ProgPattern t u]] -> [(Name, [ProgPattern t u])]
headCons = (>>= fun) 
  where
    fun :: [ProgPattern t u] -> [(Name, [ProgPattern t u])]
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
