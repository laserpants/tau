{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StrictData           #-}
module Tau.Compiler.Patterns where

import Control.Monad.Extra
import Control.Monad.Reader
import Data.Function ((&))
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
    case getPatternRep q of
        ACon con rs  ->
            let special = specialized con (patternTag <$> rs)
             in useful (special pss) (head (special [q:qs]))
        AAny -> do
            let cs = headCons pss
            isComplete <- complete (fst <$> cs)
            if isComplete
                then cs & anyM (\(con, rs) ->
                    let special = specialized con (patternTag <$> rs)
                     in useful (special pss) (head (special [q:qs]))) 
                else 
                    useful (defaultMatrix pss) qs
        AOr a b -> 
            useful pss (a:qs) ||^ useful pss (b:qs)
  where
    complete [] = pure False
    complete names@(name:_) = do
        defined <- ask
        pure undefined -- (lookupCon (defined `Env.union` builtIn) name == Set.fromList names)
    lookupCon constructors con 
        | isTupleCon con = Set.singleton con
        | otherwise = Env.findWithDefaultEmpty con constructors

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

data PatternRep t
    = ACon Name [ProgPattern t] 
    | AOr (ProgPattern t) (ProgPattern t)
    | AAny

getPatternRep :: ProgPattern t -> PatternRep t
getPatternRep = undefined

specialized :: Name -> [t] -> [[ProgPattern t]] -> [[ProgPattern t]]
specialized = undefined 

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

headCons :: [[ProgPattern t]] -> [(Name, [ProgPattern t])]
headCons = (>>= fun) 
  where
    fun :: [ProgPattern t] -> [(Name, [ProgPattern t])]
    fun [] = error "Implementation error (headCons)"
    fun (p:ps) = 
        undefined


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
exhaustive = undefined

checkExhaustive :: (MonadReader ConstructorEnv m) => Ast t -> m Bool
checkExhaustive = undefined
