{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Tau.Serialize where

import Data.Aeson
import Data.Aeson.TH
import Tau.Compiler.Error
import Tau.Compiler.Pipeline
import Tau.Core
import Tau.Eval (Eval)
import Tau.Lang
import Tau.Pretty
import Tau.Prog
import Tau.Tool
import Tau.Type
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as Text
import qualified Data.Vector as Vector
import qualified Tau.Eval as Tau

class ToRep t where
    toRep :: t -> Value

instance (ToRep t) => ToRep [t] where
    toRep ts = array (toRep <$> ts)

instance (ToRep t) => ToRep (Maybe t) where
    toRep Nothing  = object []
    toRep (Just t) = toRep t

instance ToRep Type where 
    toRep = withPretty typeJson

instance ToRep Kind where 
    toRep = withPretty kindJson

instance ToRep Prim where 
    toRep = withPretty primJson

instance (ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9) => ToRep (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9) where 
    toRep = patternRep

instance (ToRep t) => ToRep (SimplifiedPattern t) where 
    toRep = simplifiedPatternRep

instance (Functor e3, ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, ToRep t11, ToRep t12, ToRep t13, ToRep t14, ToRep t15, ToRep e1, ToRep e2, ToRep (e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3))) => ToRep (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) where
    toRep = exprRep

instance (ToRep a) => ToRep (Op1 a) where 
    toRep = op1Rep

instance (ToRep a) => ToRep (Op2 a) where 
    toRep = op2Rep

instance (ToRep t, ToRep p) => ToRep (Binding t p) where
    toRep = bindintRep

instance (ToRep a) => ToRep (Guard a) where
    toRep = guardRep

instance (ToRep t, ToRep p, ToRep a) => ToRep (Clause t p a) where
    toRep = clauseRep

instance (ToRep t, ToRep p, ToRep a) => ToRep (SimplifiedClause t p a) where
    toRep = simplifiedClauseRep

instance (ToRep e, ToRep t) => ToRep (TypeInfoT e t) where
    toRep = typeInfoRep

instance (Pretty a, ToRep a) => ToRep (PredicateT a) where
    toRep = withPretty predicateRep

instance ToRep Error where
    toRep = withPretty errorRep

instance ToRep Core where
    toRep = coreRep

instance ToRep Void where
    toRep _ = makeRep "Void" "Void" []

instance ToRep Text where
    toRep s = makeRep "Name" "Name" [String s]

instance ToRep (Tau.Value Eval) where
    toRep = valueRep

-- >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

array :: [Value] -> Value
array = Array . Vector.fromList

makeRep :: String -> String -> [Value] -> Value
makeRep type_ constructor args =
    object 
        [ "_meta"    .= [type_, constructor]
        , "children" .= args
        ]

withPretty :: (Pretty p) => (p -> Value) -> p -> Value
withPretty f p = Object (HM.insert "pretty" (String (prettyPrint p)) obj)
  where
    Object obj = f p

typeJson :: Type -> Value
typeJson = project >>> \case
    TVar k var          -> makeRep "Type" "TVar"      [toRep k, String var]
    TCon k con          -> makeRep "Type" "TCon"      [String con]
    TApp k t1 t2        -> makeRep "Type" "TApp"      [toRep k, toRep t1, toRep t2]
    TArr t1 t2          -> makeRep "Type" "TArr"      [toRep t1, toRep t2]

kindJson :: Kind -> Value
kindJson = project >>> \case
    KVar var            -> makeRep "Kind" "KVar"      [String var]
    KCon con            -> makeRep "Kind" "KCon"      [String con]
    KArr k1 k2          -> makeRep "Kind" "KArr"      [toRep k1, toRep k2]

primJson :: Prim -> Value
primJson = \case
    TUnit               -> makeRep "Prim" "TUnit"     [String "()"]
    TBool    b          -> makeRep "Prim" "TBool"     [String (if b then "True" else "False")]
    TInt     i          -> makeRep "Prim" "TInt"      [toJSON i]
    TInteger i          -> makeRep "Prim" "TInteger"  [toJSON i]
    TFloat   f          -> makeRep "Prim" "TFloat"    [toJSON f]
    TDouble  d          -> makeRep "Prim" "TDouble"   [toJSON d]
    TChar    c          -> makeRep "Prim" "TChar"     [toJSON c]
    TString  t          -> makeRep "Prim" "TString"   [toJSON t]

patternRep :: (ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9) => Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 -> Value
patternRep = project >>> \case
    PVar   t var        -> makeRep "Pattern" "PVar"   [toRep t, String var]
    PCon   t con ps     -> makeRep "Pattern" "PCon"   [toRep t, String con, toRep ps] 
    PLit   t prim       -> makeRep "Pattern" "PLit"   [toRep t, toRep prim] 
    PAs    t as p       -> makeRep "Pattern" "PAs"    [toRep t, String as, toRep p] 
    POr    t p q        -> makeRep "Pattern" "POr"    [toRep t, toRep p, toRep q] 
    PAny   t            -> makeRep "Pattern" "PAny"   [toRep t] 
    PTuple t ps         -> makeRep "Pattern" "PTuple" [toRep t, toRep ps] 
    PList  t ps         -> makeRep "Pattern" "PList"  [toRep t, toRep ps] 
    PRow   t lab p q    -> makeRep "Pattern" "PRow"   [toRep t, String lab, toRep p, toRep q] 

simplifiedPatternRep :: (ToRep t) => SimplifiedPattern t -> Value
simplifiedPatternRep = \case
    SCon   t p ps       -> makeRep "SimplifiedPattern" "SCon" [toRep t, toRep p, toRep ps]

exprRep 
  :: (Functor e3, ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, ToRep t11, ToRep t12, ToRep t13, ToRep t14, ToRep t15, ToRep e1, ToRep e2, ToRep (e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3))) 
  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3 -> Value
exprRep = project >>> \case
    EVar   t var        -> makeRep "Expr" "EVar"      [toRep t, String var]
    ECon   t con es     -> makeRep "Expr" "ECon"      [toRep t, String con, toRep es]
    ELit   t prim       -> makeRep "Expr" "ELit"      [toRep t, toRep prim]
    EApp   t es         -> makeRep "Expr" "EApp"      [toRep t, toRep es]
    EFix   t name e1 e2 -> makeRep "Expr" "EFix"      [toRep t, String name, toRep e1, toRep e2]
    ELam   t ps e       -> makeRep "Expr" "ELam"      [toRep t, toRep ps, toRep e]
    EIf    t e1 e2 e3   -> makeRep "Expr" "EIf"       [toRep t, toRep e1, toRep e2, toRep e3]
    EPat   t es cs      -> makeRep "Expr" "EPat"      [toRep t, toRep es, toRep cs]
    ELet   t bind e1 e2 -> makeRep "Expr" "ELet"      [toRep t, toRep bind, toRep e1, toRep e2]
    EFun   t cs         -> makeRep "Expr" "EFun"      [toRep t, toRep cs]
    EOp1   t op a       -> makeRep "Expr" "EOp1"      [toRep t, toRep op, toRep a]
    EOp2   t op a b     -> makeRep "Expr" "EOp2"      [toRep t, toRep op, toRep a, toRep b]
    ETuple t es         -> makeRep "Expr" "ETuple"    [toRep t, toRep es]
    EList  t es         -> makeRep "Expr" "EList"     [toRep t, toRep es]
    ERow   t lab a b    -> makeRep "Expr" "ERow"      [toRep t, String lab, toRep a, rowRep b]
    EAnn   t a          -> makeRep "Expr" "EAnn"      [toRep t, toRep a]

rowRep 
  :: (Functor e3, ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, ToRep t11, ToRep t12, ToRep t13, ToRep t14, ToRep t15, ToRep e1, ToRep e2, ToRep (e3 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3))) 
  => Maybe (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 e1 e2 e3) 
  -> Value
rowRep = \case
    Nothing             -> makeRep "Expr" "ERow"      []
    Just row            -> toRep row

op1Rep :: (ToRep t) => Op1 t -> Value
op1Rep = \case
    ONeg   t            -> makeRep "Op1" "ONeg"       [toRep t]
    ONot   t            -> makeRep "Op1" "ONot"       [toRep t]

op2Rep :: (ToRep t) => Op2 t -> Value
op2Rep = \case
    OEq    t            -> makeRep "Op2" "OEq"        [toRep t]
    ONeq   t            -> makeRep "Op2" "ONeq"       [toRep t]
    OAnd   t            -> makeRep "Op2" "OAnd"       [toRep t]
    OOr    t            -> makeRep "Op2" "OOr"        [toRep t]
    OAdd   t            -> makeRep "Op2" "OAdd"       [toRep t]
    OSub   t            -> makeRep "Op2" "OSub"       [toRep t]
    OMul   t            -> makeRep "Op2" "OMul"       [toRep t]
    ODiv   t            -> makeRep "Op2" "ODiv"       [toRep t]
    OPow   t            -> makeRep "Op2" "OPow"       [toRep t]
    OMod   t            -> makeRep "Op2" "OMod"       [toRep t]
    OLt    t            -> makeRep "Op2" "OLt"        [toRep t]
    OGt    t            -> makeRep "Op2" "OGt"        [toRep t]
    OLte   t            -> makeRep "Op2" "OLte"       [toRep t]
    OGte   t            -> makeRep "Op2" "OGte"       [toRep t]
    OLarr  t            -> makeRep "Op2" "OLarr"      [toRep t]
    ORarr  t            -> makeRep "Op2" "ORarr"      [toRep t]
    OFpipe t            -> makeRep "Op2" "OFpipe"     [toRep t]
    OBpipe t            -> makeRep "Op2" "OBpipe"     [toRep t]
    OOpt   t            -> makeRep "Op2" "OOpt"       [toRep t]
    OStrc  t            -> makeRep "Op2" "OStrc"      [toRep t]
    ONdiv  t            -> makeRep "Op2" "ONdiv"      [toRep t]

bindintRep :: (ToRep t, ToRep p) => Binding t p -> Value
bindintRep = \case
    BLet t p            -> makeRep "Binding" "BLet"   [toRep t, toRep p]
    BFun t name ps      -> makeRep "Binding" "BFun"   [toRep t, String name, toRep ps]

guardRep :: (ToRep a) => Guard a -> Value
guardRep = \case
    Guard es e          -> makeRep "Guard" "Guard"    [toRep es, toRep e]

clauseRep :: (ToRep t, ToRep p, ToRep a) => Clause t p a -> Value
clauseRep = \case
    Clause t ps e       -> makeRep "Clause" "Clause"  [toRep t, toRep ps, toRep e]

simplifiedClauseRep :: (ToRep t, ToRep p, ToRep a) => SimplifiedClause t p a -> Value
simplifiedClauseRep = \case
    SimplifiedClause t ps e -> makeRep "SimplifiedClause" "SimplifiedClause" [toRep t, toRep ps, toRep e]

typeInfoRep :: (ToRep e, ToRep t) => TypeInfoT e t -> Value
typeInfoRep = \case
    TypeInfo e t ps     -> makeRep "TypeInfoT" "TypeInfo" [toRep e, toRep t, toRep ps]

predicateRep :: (ToRep a) => PredicateT a -> Value
predicateRep = \case
    InClass name a      -> makeRep "PredicateT" "InClass" [String name, toRep a]

errorRep :: Error -> Value
errorRep = \case
    _                   -> makeRep "Error" "TODO"     []

coreRep :: Core -> Value
coreRep = cata $ \case
    CVar name           -> makeRep "Core" "CVar"      [String name]
    CLit prim           -> makeRep "Core" "CLit"      [toRep prim]
    CApp es             -> makeRep "Core" "CApp"      [array es]
    CLet name e1 e2     -> makeRep "Core" "CLet"      [String name, e1, e2]
    CLam name e         -> makeRep "Core" "CLam"      [String name, e]
    CIf  e1 e2 e3       -> makeRep "Core" "CIf"       [e1, e2, e3]
    CPat e m            -> makeRep "Core" "CPat"      [e, array (coreClausesRep <$> m)]

coreClausesRep :: ([Name], Value) -> Value
coreClausesRep (names, value) = array [array (String <$> names), value]

valueRep :: Tau.Value Eval -> Value
valueRep = \case
    Tau.Value prim      -> makeRep "Value" "Prim"     [toRep prim]
    Tau.Data con args   -> makeRep "Value" "Data"     [String con, toRep args]
    Tau.PrimFun f _ vs  -> makeRep "Value" "PrimFun"  [String f, String "<<internal>>", toRep vs]
    Tau.Closure f _ _   -> makeRep "Value" "Closure"  [String f, String "<<internal>>", String "<<internal>>"]
