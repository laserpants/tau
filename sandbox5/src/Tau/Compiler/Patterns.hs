{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StrictData           #-}
module Tau.Compiler.Patterns where

import Control.Monad.Extra
import Control.Monad.Reader
import Data.Function ((&))
import Data.Maybe (fromMaybe)
import Tau.Lang
import Tau.Prog
import Tau.Tooling
import Tau.Type
import qualified Data.Set.Monad as Set
import qualified Tau.Env as Env

useful :: (MonadReader ConstructorEnv m) => [[ProgPattern t]] -> [ProgPattern t] -> m Bool
useful [] _ = pure True     -- Zero rows (0x0 matrix)
useful (p1:_) qs 
    | null p1 = pure False  -- One or more rows but no columns
    | null qs = error "Implementation error (useful)"
useful pss (q:qs) =
    case groupPatterns q of
        ConGroup con rs  ->
            let special = specialized con (patternTag <$> rs)
             in useful (special pss) (head (special [q:qs]))
        WildcardPattern -> do
            let cs = headCons pss
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) ->
                    let special = specialized con (patternTag <$> rs)
                     in useful (special pss) (head (special [q:qs]))) 
                else 
                    useful (defaultMatrix pss) qs
        OrPattern a b -> 
            useful pss (a:qs) ||^ useful pss (b:qs)
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

groupPatterns :: ProgPattern t -> PatternGroup t
groupPatterns = project >>> \case
    PCon _ con rs    -> ConGroup con rs
    PTuple t elems   -> groupPatterns (foldTuple t elems)
    PList  t elems   -> groupPatterns (foldList t elems)
    PRow   t lab p q -> groupPatterns (foldRowPat t lab p q)
    PAs _ _ a        -> groupPatterns a
    POr _ a b        -> OrPattern a b
    _                -> WildcardPattern

specialized :: Name -> [t] -> [[ProgPattern t]] -> [[ProgPattern t]]
specialized name ts = (rec =<<)
  where
    rec [] = error "Implementation error (specialized)"
    rec (p:ps) =
        case project p of
            PCon _ con rs
                | con == name -> [rs <> ps]
                | otherwise   -> []

            PTuple t elems    -> rec (foldTuple t elems:ps)
            PList  t elems    -> rec (foldList t elems:ps)
            PRow   t lab p q  -> rec (foldRowPat t lab p q:ps)
            PAs _ _ q         -> rec (q:ps)
            POr _ p1 p2       -> rec (p1:ps) <> rec (p2:ps)
            _                 -> [(anyPat <$> ts) <> ps]

defaultMatrix :: [[ProgPattern t]] -> [[ProgPattern t]]
defaultMatrix = (fun =<<)
  where
    fun :: [ProgPattern t] -> [[ProgPattern t]]
    fun (p:ps) =
        case project p of
            PCon{}    -> []
            PTuple{}  -> []
            PList{}   -> []
            PRow{}    -> []
            PLit{}    -> []
            PAnn _ p  -> fun (p:ps)
            PAs _ _ q -> fun (q:ps)
            POr _ q r -> fun (q:ps) <> fun (r:ps)
            _         -> [ps]

foldTuple :: t -> [ProgPattern t] -> ProgPattern t
foldTuple t elems = conPat t (tupleCon (length elems)) elems

foldList :: t -> [ProgPattern t] -> ProgPattern t
foldList t = foldr (listPatCons t) (conPat t "[]" [])

headCons :: [[ProgPattern t]] -> [(Name, [ProgPattern t])]
headCons = (>>= fun) 
  where
    fun :: [ProgPattern t] -> [(Name, [ProgPattern t])]
    fun [] = error "Implementation error (headCons)"
    fun (p:ps) = 
        case project p of
            PLit   _ p               -> [(prim p, [])]
            PCon   _ name rs         -> [(name, rs)]
            PTuple t elems           -> fun (foldTuple t elems:ps)
            PList  t elems           -> fun (foldList t elems:ps)
            PRow   t lab p q         -> fun (foldRowPat t lab p q:ps)
            PAs    _ _ q             -> fun (q:ps)
            POr    _ a b             -> fun (a:ps) <> fun (b:ps)
            _                        -> []

    prim (TBool True)  = "#True"
    prim (TBool False) = "#False"
    prim TUnit         = "#()"
    prim TInt{}        = "#Int"
    prim TInteger{}    = "#Integer"
    prim TFloat{}      = "#Float"
    prim TDouble{}     = "#Double"
    prim TChar{}       = "#Char"
    prim TString{}     = "#String"

exhaustive :: (MonadReader ConstructorEnv m) => [[ProgPattern t]] -> m Bool
exhaustive []         = pure False
exhaustive pss@(ps:_) = not <$> useful pss (anyPat . patternTag <$> ps)

-- | Determine if all patterns in the expression are exhaustive.
--
checkExhaustive :: (MonadReader ConstructorEnv m) => ProgExpr () -> m Bool
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

clausesAreExhaustive :: (MonadReader ConstructorEnv m) => [Clause () (ProgPattern ()) (ProgExpr ())] -> m Bool
clausesAreExhaustive = exhaustive . fmap toMatrix
  where
    toMatrix (Clause _ p guards)
        | null guards           = [p]
        | any isCatchAll guards = [p]
    toMatrix _ = 
        []

    isCatchAll (Guard [ ] _)             = True
    isCatchAll (Guard [b] _) | b == true = True where true = litExpr () (TBool True)
    isCatchAll _                         = False
