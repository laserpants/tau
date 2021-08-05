{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Tau.Serializers where

import Control.Arrow ((<<<), (>>>))
import Data.Aeson
import Data.Functor.Foldable (cata, para, project, embed)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Void
import Tau.Misc
import Tau.Prettyprinters
import Tau.Util
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Vector as Vector

class ToRep t where
    toRep :: t -> Value

instance (ToRep t) => ToRep [t] where
    toRep ts = array (toRep <$> ts)

instance ToRep Type where
    toRep = withPretty typeJson

instance ToRep Kind where
    toRep = withPretty kindJson

instance ToRep Prim where
    toRep = withPretty primJson

instance ToRep () where
    toRep _ = makeRep "()" "()" []

instance (ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, Pretty t10) => ToRep (Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10) where
    toRep = withPretty patternRep

instance (Functor e2, Functor e4, ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, ToRep t11, ToRep t12, ToRep t13, ToRep t14, ToRep t15, ToRep t16, ToRep t17, ToRep e1, ToRep (e2 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)), ToRep e3, ToRep (e4 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)), FunArgsRep e1, Pretty e1, Pretty t17) => ToRep (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4) where
    toRep = withPretty exprRep

instance (ToRep a) => ToRep (Op1 a) where
    toRep = withPretty op1Rep

instance (ToRep a) => ToRep (Op2 a) where
    toRep = withPretty op2Rep

instance (ToRep t, ToRep p) => ToRep (Binding t p) where
    toRep = bindingRep

instance (Pretty p, Pretty a, ToRep t, ToRep p, ToRep a) => ToRep (Clause t p a) where
    toRep = withPretty clauseRep

instance (ToRep a) => ToRep (Choice a) where
    toRep = choiceRep

instance ToRep Predicate where
    toRep = withPretty predicateRep

instance ToRep (PredicateT Name) where
    toRep = withPretty predicateRep

instance (ToRep t, ToRep e) => ToRep (TypeInfoT [e] t) where
    toRep = typeInfoRep

instance ToRep Text where
    toRep = textJson

instance ToRep Error where
    toRep = errorRep

instance ToRep UnificationError where
    toRep = unificationErrorRep

instance ToRep Void where
    toRep _ = ""

typeJson :: Type -> Value
typeJson = project >>> \case
    TVar k var          -> makeRep "Type" "TVar"       [toRep k, String var]
    TCon k con          -> makeRep "Type" "TCon"       [toRep k, String con]
    TApp k t1 t2        -> makeRep "Type" "TApp"       [toRep k, toRep t1, toRep t2]
    TArr t1 t2          -> makeRep "Type" "TArr"       [toRep t1, toRep t2]
    TRow label t1 t2    -> makeRep "Type" "TRow"       [String label, toRep t1, toRep t2]

kindJson :: Kind -> Value
kindJson = project >>> \case
    KVar var            -> makeRep "Kind" "KVar"       [String var]
    KCon con            -> makeRep "Kind" "KCon"       [String con]
    KArr k1 k2          -> makeRep "Kind" "KArr"       [toRep k1, toRep k2]

primJson :: Prim -> Value
primJson = \case
    TUnit               -> makeRep "Prim" "TUnit"      [String "()"]
    TBool    a          -> makeRep "Prim" "TBool"      [String (if a then "True" else "False")]
    TInt     a          -> makeRep "Prim" "TInt"       [toJSON a]
    TInteger a          -> makeRep "Prim" "TInteger"   [toJSON a]
    TFloat   a          -> makeRep "Prim" "TFloat"     [toJSON a]
    TDouble  a          -> makeRep "Prim" "TDouble"    [toJSON a]
    TChar    a          -> makeRep "Prim" "TChar"      [toJSON a]
    TString  a          -> makeRep "Prim" "TString"    [toJSON a]
    TSymbol  a          -> makeRep "Prim" "TSymbol"    [toJSON a]

patternRep
  :: (ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, Pretty t10)
  => Pattern t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  -> Value
patternRep = project >>> \case
    PVar    t var       -> makeRep "Pattern" "PVar"    [toRep t, String var]
    PCon    t con ps    -> makeRep "Pattern" "PCon"    [toRep t, String con, toRep ps]
    PLit    t prim      -> makeRep "Pattern" "PLit"    [toRep t, toRep prim]
    PAs     t as p      -> makeRep "Pattern" "PAs"     [toRep t, String as, toRep p]
    POr     t p q       -> makeRep "Pattern" "POr"     [toRep t, toRep p, toRep q]
    PAny    t           -> makeRep "Pattern" "PAny"    [toRep t]
    PTuple  t ps        -> makeRep "Pattern" "PTuple"  [toRep t, toRep ps]
    PList   t ps        -> makeRep "Pattern" "PList"   [toRep t, toRep ps]
    PRow    t lab a b   -> makeRep "Pattern" "PRow"    [toRep t, String lab, toRep a, toRep b]
    PRecord t p         -> makeRep "Pattern" "PRecord" [toRep t, toRep p]
    PAnn    t p         -> makeRep "Pattern" "PAnn"    [toRep t, toRep p]

exprRep
  :: (Functor e2, Functor e4, ToRep t1, ToRep t2, ToRep t3, ToRep t4, ToRep t5, ToRep t6, ToRep t7, ToRep t8, ToRep t9, ToRep t10, ToRep t11, ToRep t12, ToRep t13, ToRep t14, ToRep t15, ToRep t16, ToRep t17, ToRep e1, ToRep e3, ToRep (e2 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)), ToRep (e4 (Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4)), FunArgsRep e1, Pretty e1, Pretty t17)
  => Expr t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 e1 e2 e3 e4
  -> Value
exprRep = project >>> \case
    EVar    t var       -> makeRep "Expr" "EVar"       [toRep t, String var]
    EHole   t           -> makeRep "Expr" "EHole"      [toRep t]
    ECon    t con es    -> makeRep "Expr" "ECon"       [toRep t, String con, toRep es]
    ELit    t prim      -> makeRep "Expr" "ELit"       [toRep t, toRep prim]
    EApp    t es        -> makeRep "Expr" "EApp"       [toRep t, toRep es]
    EFix    t n e1 e2   -> makeRep "Expr" "EFix"       [toRep t, String n, toRep e1, toRep e2]
    ELam    t ps e      -> makeRep "Expr" "ELam"       [toRep t, toFunArgsRep ps, toRep e]
    EIf     t e1 e2 e3  -> makeRep "Expr" "EIf"        [toRep t, toRep e1, toRep e2, toRep e3]
    EPat    t es cs     -> makeRep "Expr" "EPat"       [toRep t, toRep es, toRep cs]
    ELet    t b e1 e2   -> makeRep "Expr" "ELet"       [toRep t, toRep b, toRep e1, toRep e2]
    EFun    t cs        -> makeRep "Expr" "EFun"       [toRep t, toRep cs]
    EOp1    t op a      -> makeRep "Expr" "EOp1"       [toRep t, toRep op, toRep a]
    EOp2    t op a b    -> makeRep "Expr" "EOp2"       [toRep t, toRep op, toRep a, toRep b]
    ETuple  t es        -> makeRep "Expr" "ETuple"     [toRep t, toRep es]
    EList   t es        -> makeRep "Expr" "EList"      [toRep t, toRep es]
    ERow    t lab a b   -> makeRep "Expr" "ERow"       [toRep t, String lab, toRep a, toRep b]
    ERecord t e         -> makeRep "Expr" "ERecord"    [toRep t, toRep e]
    EAnn    t a         -> makeRep "Expr" "EAnn"       [toRep t, toRep a]

op1Rep :: (ToRep t) => Op1 t -> Value
op1Rep = \case
    ONeg   t            -> makeRep "Op1" "ONeg"        [toRep t]
    ONot   t            -> makeRep "Op1" "ONot"        [toRep t]

op2Rep :: (ToRep t) => Op2 t -> Value
op2Rep = \case
    OEq    t            -> makeRep "Op2" "OEq"         [toRep t]
    ONeq   t            -> makeRep "Op2" "ONeq"        [toRep t]
    OAnd   t            -> makeRep "Op2" "OAnd"        [toRep t]
    OOr    t            -> makeRep "Op2" "OOr"         [toRep t]
    OAdd   t            -> makeRep "Op2" "OAdd"        [toRep t]
    OSub   t            -> makeRep "Op2" "OSub"        [toRep t]
    OMul   t            -> makeRep "Op2" "OMul"        [toRep t]
    ODiv   t            -> makeRep "Op2" "ODiv"        [toRep t]
    OPow   t            -> makeRep "Op2" "OPow"        [toRep t]
    OMod   t            -> makeRep "Op2" "OMod"        [toRep t]
    OLt    t            -> makeRep "Op2" "OLt"         [toRep t]
    OGt    t            -> makeRep "Op2" "OGt"         [toRep t]
    OLte   t            -> makeRep "Op2" "OLte"        [toRep t]
    OGte   t            -> makeRep "Op2" "OGte"        [toRep t]
    OLarr  t            -> makeRep "Op2" "OLarr"       [toRep t]
    ORarr  t            -> makeRep "Op2" "ORarr"       [toRep t]
    OFpip  t            -> makeRep "Op2" "OFpipe"      [toRep t]
    OBpip  t            -> makeRep "Op2" "OBpipe"      [toRep t]
    OOpt   t            -> makeRep "Op2" "OOpt"        [toRep t]
    OStr   t            -> makeRep "Op2" "OStr"        [toRep t]
    ODot   t            -> makeRep "Op2" "ODot"        [toRep t]
    OField t            -> makeRep "Op2" "OField"      [toRep t]

bindingRep :: (ToRep t, ToRep p) => Binding t p -> Value
bindingRep = \case
    BPat t p            -> makeRep "Binding" "BPat"    [toRep t, toRep p]
    BFun t name ps      -> makeRep "Binding" "BFun"    [toRep t, String name, toRep ps]

clauseRep :: (ToRep t, ToRep p, ToRep a) => Clause t p a -> Value
clauseRep = \case
    Clause t ps e       -> makeRep "Clause" "Clause"   [toRep t, toRep ps, toRep e]

choiceRep :: (ToRep a) => Choice a -> Value
choiceRep = \case
    Choice es e         -> makeRep "Choice" "Choice"   [toRep es, toRep e]

predicateRep :: (ToRep a) => PredicateT a -> Value
predicateRep = \case
    InClass name a      -> makeRep "PredicateT" "InClass" [String name, toRep a]

typeInfoRep :: (ToRep t, ToRep e) => TypeInfoT [e] t -> Value
typeInfoRep = \case
    TypeInfo e t ps     -> makeRep "TypeInfoT" "TypeInfo" [toRep e, toRep t, toRep ps]

class FunArgsRep f where
    toFunArgsRep :: f -> Value

instance FunArgsRep Text where
    toFunArgsRep t = array [toRep t]

instance (ToRep t, ToRep u, Pretty u) => FunArgsRep [ProgPattern t u] where
    toFunArgsRep = array . fmap toRep

textJson :: Text -> Value
textJson s = makeRep "Name" "Name" [String s]

errorRep :: Error -> Value
errorRep = \case
    UnificationError err                -> String "UnificationError"
    NotInScope name                     -> String "NotInScope"
    ConstructorNotInScope name          -> String "ConstructorNotInScope"
    NoSuchClass name                    -> String "NoSuchClass"
    MissingInstance name t              -> String "MissingInstance"
    PatternArityMismatch name m n       -> String "PatternArityMismatch"
    NonBooleanGuard expr                -> String "NonBooleanGuard"

unificationErrorRep :: UnificationError -> Value
unificationErrorRep = \case
    InfiniteType                        -> String "InfiniteType"
    InfiniteKind                        -> String "InfiniteKind"
    IncompatibleTypes                   -> String "IncompatibleTypes"
    IncompatibleKinds                   -> String "IncompatibleKinds"
    CannotMerge                         -> String "CannotMerge"

-------------------------------------------------------------------------------

array :: [Value] -> Value
array = Array . Vector.fromList
{-# INLINE array #-}

makeRep :: String -> String -> [Value] -> Value
makeRep type_ constructor args = object
    [ "meta"     .= [type_, constructor]
    , "children" .= args ]

withPretty :: (Pretty p) => (p -> Value) -> p -> Value
withPretty f p = Object (HashMap.insert "toStr" (String (prettyT p)) obj)
  where
    Object obj = f p
