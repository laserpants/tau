{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader
import Control.Monad.State
import Data.Either (isLeft, isRight)
import Data.Fix (Fix(..))
import Data.Functor.Foldable (cata, para, embed)
import Data.Functor.Identity
import Data.Map.Strict (Map)
import Data.Maybe (fromJust)
import Data.Text (Text, pack, unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Void
import Stuff
import Tau.Eval
import Tau.Misc
import Tau.Parse
import Tau.Prettyprinters
import Tau.Tree
import Tau.Util (Name, runSupplyNats, prettyT, prettyW, renderDoc)
import Test.Hspec hiding (describe, it)
import Text.Megaparsec
import TextShow
import qualified Data.Map.Strict as Map
import qualified Data.Text  as Text
import qualified Tau.Env as Env
import qualified Test.Hspec as Hspec

describe :: Text -> SpecWith () -> SpecWith ()
describe = Hspec.describe . unpack

it :: (Example a) => Text -> a -> SpecWith (Arg a)
it = Hspec.it . unpack

main :: IO ()
main =
    hspec $ do
        describe "Unification"    testUnification
        describe "Substitution"   testSubstitution
        describe "Type vars"      testTypeVars
        describe "Kind of"        testKindOf
        describe "toPolytype"     testToPolytype
        describe "tupleCon"       testTupleCon
        describe "Type inference" testTypeInference
        describe "Prettyprinters" testPrettyprinters
        describe "Flight"         testFlight
        describe "Parse"          testParse

_a :: Type
_a = tVar kTyp "a"

_b :: Type
_b = tVar kTyp "b"

_c :: Type
_c = tVar kTyp "c"

-------------------------------------------------------------------------------

-- Unification tests

runUnify :: Type -> Type -> Either UnificationError (Substitution Type, Substitution Kind)
runUnify t1 t2 = runSupplyNats (runExceptT (unifyTypes t1 t2))

runMatch :: Type -> Type -> Either UnificationError (Substitution Type, Substitution Kind)
runMatch t1 t2 = runSupplyNats (runExceptT (matchTypes t1 t2))

testDescription :: Type -> Type -> Text
testDescription t1 t2 = "The types " <> prettyT t1 <> " and " <> prettyT t2

succeedWithResult
  :: (Substitutable Type a1, Substitutable Type a2)
  => Type
  -> Type
  -> Either UnificationError (Substitution a1, Substitution a2)
  -> SpecWith ()
succeedWithResult t1 t2 result =
    describe (testDescription t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types" $ do
            let Right (typeSub, kindSub) = result
                r1 = apply kindSub (apply typeSub t1)
                r2 = apply kindSub (apply typeSub t2)
            canonicalRep r1 == canonicalRep r2

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = succeedWithResult t1 t2 (runUnify t1 t2)

succeedMatchTypes :: Type -> Type -> SpecWith ()
succeedMatchTypes t1 t2 = succeedWithResult t1 t2 (runMatch t1 t2)

canonicalRep :: Type -> Type
canonicalRep = cata $ \case
    TVar k var       -> tVar k var
    TCon k con       -> tCon k con
    TApp k t1 t2     -> tApp k t1 t2
    TArr t1 t2       -> tArr t1 t2
    TRow label t1 t2 -> toCanonical (tRow label t1 t2)
  where
    toCanonical t =
        fromMap (baseRow t) (foldr (uncurry f) mempty (rowFields t))

    fromMap :: Type -> Map Name [Type] -> Type
    fromMap = Map.foldrWithKey (flip . foldr . tRow)

    rowFields :: Type -> [(Name, Type)]
    rowFields = para $ \case
        TRow label ty rest             -> (label, fst ty):snd rest
        _                              -> []

    baseRow :: Type -> Type
    baseRow = cata $ \case
        TRow _ _ r                     -> r
        t                              -> embed t

    f name ty = Map.insertWith (<>) name [ty]

failUnifyTypes :: Type -> Type -> SpecWith ()
failUnifyTypes t1 t2 = do
    let result = runUnify t1 t2
    describe (testDescription t1 t2) $
        it "✗ fails to unify" $
            isLeft result

failMatchTypes :: Type -> Type -> SpecWith ()
failMatchTypes t1 t2 = do
    let result = runMatch t1 t2
    describe (testDescription t1 t2) $
        it "✗ fails to match" $
            isLeft result

testUnification :: SpecWith ()
testUnification = do

    succeedUnifyTypes
        (_a `tArr` _b)
        (tInt `tArr` tInt)

    failUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tBool)

    succeedUnifyTypes
        (_a `tArr` _a)
        (tInt `tArr` tInt)

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _a)

    succeedUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (_a `tArr` tInt `tArr` _b)

    failUnifyTypes
        (_a `tArr` _b `tArr` _a)
        (tInt `tArr` tInt `tArr` tBool)

    succeedUnifyTypes
        (tList _a)
        (tList tInt)

    succeedUnifyTypes
        (tList _a)
        (tList _b)

    failUnifyTypes
        (tList _a)
        (tPair _a _b)

    succeedUnifyTypes
        (tPair _a _a)
        (tPair _a _b)

    failUnifyTypes
        (tPair _a _a)
        (tPair tInt tBool)

    failUnifyTypes
        (tList _a)
        tInt

    succeedUnifyTypes
        tInt
        tInt

    failUnifyTypes
        tUnit
        tInt

    describe "• Row types" $ do

        succeedUnifyTypes
            -- { name : a26 | a27 }
            (tRow "name" (tVar kTyp "a26") (tVar kRow "a27"))
            -- { id : Int, name : String }
            (tRow "id" tInt (tRow "name" tString tRowNil))

        succeedUnifyTypes
            (tArr (tRow "name" (tVar kTyp "a26") (tVar kRow "a27")) (tVar kTyp "a"))
            (tArr (tRow "id" tInt (tRow "name" tString tRowNil)) tInt)

        succeedUnifyTypes
            (tArr (tRecord (tRow "name" (tVar kTyp "a26") (tVar kRow "a27"))) (tVar kTyp "a"))
            (tArr (tRecord (tRow "id" tInt (tRow "name" tString tRowNil))) tInt)

        failUnifyTypes
            (tRow "name" tString (tRow "id" tInt tRowNil))
            (tRow "id" tString (tRow "name" tInt tRowNil))

        succeedUnifyTypes
            (tRow "name" tString (tRow "id" tInt tRowNil))
            (tRow "id" tInt (tRow "name" tString tRowNil))

        succeedUnifyTypes
            (tRow "x" tInt (tVar kRow "r"))
            (tRow "x" tInt (tVar kRow "r"))

        failUnifyTypes
            (tRow "x" tInt (tVar kRow "r"))
            (tRow "y" tInt (tVar kRow "r"))

        succeedUnifyTypes
            (tRow "x" tInt (tVar kRow "r"))
            (tRow "x" tInt (tVar kRow "s"))

        succeedUnifyTypes
            (tRow "id" tInt (tVar kRow "r"))
            (tRow "id" tInt (tRow "name" tString tRowNil))

        succeedUnifyTypes
            (tRow "id" tInt (tRow "name" tString tRowNil))
            (tRow "id" tInt (tVar kRow "r"))

        succeedUnifyTypes
            (tRow "id" tInt (tRow "password" tString (tRow "name" tString tRowNil)))
            (tRow "id" tInt (tVar kRow "r"))

        succeedUnifyTypes
            (tRow "id" tInt (tRow "password" tString (tRow "name" tString tRowNil)))
            (tVar kRow "r")

        failUnifyTypes
            (tRow "id" tInt (tRow "password" tString (tRow "name" tString tRowNil)))
            (tVar kTyp "r")  --- Note: Not a row kind!

        succeedUnifyTypes
            (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
            (tRow "shoeSize" tFloat (tRow "id" tInt (tRow "name" tString tRowNil)))

        succeedUnifyTypes
            -- { name : String, shoeSize : Float }
            (tRow "name" tString (tRow "shoeSize" tFloat tRowNil))
            -- { shoeSize : Float | r }
            (tRow "shoeSize" tFloat (tVar kRow "r"))

        succeedUnifyTypes
            -- { name : String, id : Int, shoeSize : Float }
            (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
            -- { shoeSize : Float, id : Int | r }
            (tRow "shoeSize" tFloat (tRow "id" tInt (tVar kRow "r")))

        succeedUnifyTypes
            -- { name : String, id : Int, shoeSize : Float }
            (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
            -- { shoeSize : Float | r }
            (tRow "shoeSize" tFloat (tVar kRow "r"))

        succeedUnifyTypes
            (tRow "shoeSize" tFloat (tVar kRow "r"))
            (tRow "name" tString (tRow "shoeSize" tFloat tRowNil))

        succeedUnifyTypes
            (tRow "shoeSize" tFloat (tRow "id" tInt (tVar kRow "r")))
            (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))

        succeedUnifyTypes
            (tRow "name" tString (tRow "id" tInt (tRow "shoeSize" tFloat tRowNil)))
            (tRow "name" tString (tRow "id" tInt (tVar kRow "r")))

        succeedUnifyTypes
            (tRow "name" tString (tRow "id" tInt tRowNil))
            (tRow "name" tString (tRow "id" (tVar kTyp "a") tRowNil))

        succeedUnifyTypes
            (tRow "name" tString (tRow "id" (tVar kTyp "a") tRowNil))
            (tRow "name" tString (tRow "id" tInt tRowNil))

    describe "• Matching (one-way unification)" $ do

        succeedMatchTypes
            (tVar kTyp "a")
            tInt

        failMatchTypes
            tInt
            (tVar kTyp "a")

-------------------------------------------------------------------------------

-- Substitution tests

succeedApplyTo :: Substitution Type -> Type -> Type -> SpecWith ()
succeedApplyTo sub ty res =
    describe ("apply " <> prettyT (show sub) <> " to " <> prettyT ty) $ do
        it ("✔ returns: " <> prettyT res)
            (apply sub ty == res)

succeedComposeAndApplyTo :: Substitution Type -> Substitution Type -> Type -> Type -> SpecWith ()
succeedComposeAndApplyTo sub1 sub2 ty res =
    describe ("apply to " <> prettyT ty) $ do
        it ("✔ returns: "  <> prettyT res)
            (apply (compose sub1 sub2) ty == res)

testSubstitution :: SpecWith ()
testSubstitution = do

    describe "• Apply to" $ do

        succeedApplyTo
            (mapsTo "a" tInt)
            _a
            tInt

        succeedApplyTo
            (mapsTo "a" tInt)
            (_a `tArr` _b)
            (tInt `tArr` _b)

        succeedApplyTo
            (mapsTo "a" tInt)
            (_a `tArr` _a)
            (tInt `tArr` tInt)

        succeedApplyTo
            (mapsTo "a" tInt)
            tInt
            tInt

    describe "• Compose and apply to" $ do

        succeedComposeAndApplyTo
            (fromList [ ("a", tInt) ])
            (fromList [ ("b", tBool) ])
            _a
            tInt

        succeedComposeAndApplyTo
            (fromList [ ("a", tInt) ])
            (fromList [ ("b", tBool) ])
            _b
            tBool

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tInt) ])
            _a
            tInt

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tInt) ])
            _b
            tBool

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tInt) ])
            (_a `tArr` _b)
            (tInt `tArr` tBool)

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tVar kTyp "b") ])
            _a
            tBool

        succeedComposeAndApplyTo
            (fromList [ ("b", tBool) ])
            (fromList [ ("a", tVar kTyp "b") ])
            _b
            tBool

        succeedComposeAndApplyTo
            (compose (fromList [ ("a3", tVar kTyp "a4") ]) (fromList [ ("a2", tVar kTyp "a3") ]))
            (fromList [ ("a1", tVar kTyp "a2") ])
            (tVar kTyp "a1")
            (tVar kTyp "a4")

-------------------------------------------------------------------------------

-- Type tests

succeedHasFreeTypeVars :: Type -> [(Name, Kind)] -> SpecWith ()
succeedHasFreeTypeVars ty vars =
    describe ("The free type variables in " <> prettyT ty) $
        it ("✔ are [" <> Text.intercalate ", " (renderDoc . prettyTypePair <$> vars) <> "]")
            (typeVars ty == vars)
  where
    prettyTypePair (n, k) = pretty n <+> ":" <+> pretty k

testTypeVars :: SpecWith ()
testTypeVars = do

    succeedHasFreeTypeVars
        _a
        [("a", kTyp)]

    succeedHasFreeTypeVars
        (_a `tArr` _b)
        [("a", kTyp), ("b", kTyp)]

    succeedHasFreeTypeVars
        (tList _a `tArr` _b)
        [("a", kTyp), ("b", kTyp)]

    succeedHasFreeTypeVars
        tInt
        []

    succeedHasFreeTypeVars
        (tApp kTyp (tVar kFun "m") _a)
        [("m", kFun), ("a", kTyp)]

testKindOf :: SpecWith ()
testKindOf = do

    describe "The kind of bool" $ do
        it "✔ is *"
            (kindOf tBool == kTyp)

    describe "The kind of (int -> int)" $ do
        it "✔ is *"
            (kindOf (tInt `tArr` tInt) == kTyp)

    describe "The kind of (List a)" $ do
        it "✔ is *"
            (kindOf (tList _a) == kTyp)

    describe "The kind of (List int)" $ do
        it "✔ is *"
            (kindOf (tList tInt) == kTyp)

    describe "The kind of List" $ do
        it "✔ is * -> *"
            (kindOf tListCon == kFun)

testToPolytype :: SpecWith ()
testToPolytype = do

    describe "Upgrading a type variable" $ do
        it "✔ returns the same type"
            (toPolytype _a == (tVar kTyp "a" :: Polytype))

    describe "Upgrading a type constructor" $ do
        it "✔ returns the same type"
            (toPolytype tInt == (tInt :: Polytype))

testTupleCon :: SpecWith ()
testTupleCon = do

    describe "The pair constructor" $ do
        it "✔ is (,)"
            (tupleCon 2 == "(,)")

    describe "The 3-tuple constructor" $ do
        it "✔ is (,,)"
            (tupleCon 3 == "(,,)")

    describe "The 4-tuple constructor" $ do
        it "✔ is (,,,)"
            (tupleCon 4 == "(,,,)")

-------------------------------------------------------------------------------

-- Type inference tests

succeedInferExpr :: ProgExpr () Type -> Type -> [Error] -> SpecWith ()
succeedInferExpr expr ty errs =
    describe ("The inferred type of the expression " <> prettyT expr) $ do
        it ("✔ is unifiable with " <> prettyT ty) $
            isRight res
        if null errs
            then
                it "✔ contains no errors" $
                    not (hasErrors e2)
            else
                it ("✔ contains errors: " <> pack (show errs)) $
                    and [err `elem` allErrors e2 | err <- errs]
  where
    (Ast e, (typeSub, kindSub, context)) =
        runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType expr)

    res = runMatch ty (typeOf (applyBoth (typeSub, kindSub) e))
    e1  = runReader (exhaustivePatternsCheck e) testConstructorEnv
    (e2, _) = runSupplyNats (runReaderT (ambiguityCheck context e1) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))

testTypeInference :: SpecWith ()
testTypeInference = do

    succeedInferExpr
        (varExpr () "x")
        (tVar kTyp "a")
        [NotInScope "x"]

    succeedInferExpr
        (appExpr () [varExpr () "id", litExpr () (TInt 5)])
        (tVar kTyp "a")
        []

    succeedInferExpr
        (appExpr () [varExpr () "id", annExpr tInt (litExpr () (TBig 5))])
        tInt
        []

    succeedInferExpr
        (appExpr () [varExpr () "id", litExpr () (TBool True)])
        tBool
        []

    succeedInferExpr
        (varExpr () "id")
        (tVar kTyp "a" `tArr` tVar kTyp "a")
        []

    succeedInferExpr
        (conExpr () "(::)" [litExpr () (TBool True), conExpr () "[]" []])
        (tList tBool)
        []

    succeedInferExpr
        (listExpr () [litExpr () (TBool True)])
        (tList tBool)
        []

    succeedInferExpr
        -- let x = () in x
        (letExpr () (BPat () (varPat () "x")) (litExpr () TUnit) (varExpr () "x"))
        tUnit
        []

    succeedInferExpr
        -- let x = 5 in x
        (letExpr () (BPat () (varPat () "x")) (litExpr () (TBig 5)) (varExpr () "x"))
        (tVar kTyp "a")
        []

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))]))
        tInt
        []

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (varExpr () "f"))
        (tVar kTyp "a" `tArr` tVar kTyp "a")
        []

    succeedInferExpr
        (funExpr () [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "[]" []] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] [Choice [] (litExpr () (TBool True))] ])
        (tList (tVar kTyp "a") `tArr` tBool)
        []

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (litExpr () (TBig 11)) (lamExpr () [varPat () "x"] (appExpr () [varExpr () "show", appExpr () [varExpr () "read", varExpr () "x"]])))
        (tString `tArr` tString)
        [AmbiguousType "Read" (tVar kTyp "$v15"), AmbiguousType "Show" (tVar kTyp "$v15")]

    describe "• Records" $ do

        succeedInferExpr
            -- (let r = { a = 1 : Int, b = 2 : Int } in ({ a = a | z }) => a)({ a = 5 : Int })
            (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
            tInt
            []

        -- let f(z) = { a = 1 : Int | z } in f({ b = 2 : Int })
        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z")))
                (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
            -- { a : Int, b : Int }
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))
            []

        -- ((z) => { a = 1 : Int | z })({ b = 2 : Int })
        succeedInferExpr
            (appExpr () [lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))), recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))
            []

        -- (z) => { a = 1 : Int | z }
        succeedInferExpr
            (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))))
            (tRecord (tVar kRow "r") `tArr` tRecord (tRow "a" tInt (tVar kRow "r")))
            []

        -- ({ a = a | z }) => z
        succeedInferExpr
            (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z"))
            -- { a : a | r } -> { r }
            (tRecord (tRow "a" (tVar kTyp "a") (tVar kRow "r")) `tArr` tRecord (tVar kRow "r"))
            []

        -- (({ a = a | z }) => z)({ a = 1 })
        succeedInferExpr
            (appExpr () [lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z"), recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" []))])
            -- {}
            (tRecord (tCon kRow "{}"))
            []

        -- (({ a = a | z }) => z)({ a = 1, b = 2, d = 3 })
        succeedInferExpr
            (appExpr ()
                [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")
                , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1)))
                                (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2)))
                                (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3)))
                                (conExpr () "{}" [])))) ])
            (tRecord (tRow "b" tInt (tRow "d" tInt tRowNil)))
            []

        succeedInferExpr
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (varExpr () "withDefault"))
            (tVar kTyp "a" `tArr` tApp kTyp (tCon kFun "Option") (tVar kTyp "a") `tArr` tVar kTyp "a")
            []

        -- { a = 1 : Int, b = 2 : Int }.a
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
            tInt
            []

        -- { a = (), b = 2 }.a
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
            tUnit
            []

        -- let c = (_ => True) in { a = (), b = 2 }.c
        succeedInferExpr
            (letExpr () (BPat () (varPat () "c"))
                (lamExpr () [anyPat ()] (litExpr () (TBool True)))
                (op2Expr () (ODot ()) (varExpr () "c") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))))))
            tBool
            []

        -- let c(_) = true in { a = (), b = 2 }.c
        succeedInferExpr
            (letExpr () (BFun () "c" [anyPat ()])
                (litExpr () (TBool True))
                (op2Expr () (ODot ()) (varExpr () "c") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))))))
            tBool
            []

        -- { a = { b = { c = \"d\" } } }.a.b.c
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "c") (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (recordExpr () (rowExpr () "b" (recordExpr () (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" []))) (conExpr () "{}" []))) (conExpr () "{}" []))))))
            tString
            []

        -- { a = { b = { c = \"d\" } } }.a.b
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (recordExpr () (rowExpr () "b" (recordExpr () (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" []))) (conExpr () "{}" []))) (conExpr () "{}" [])))))
            (tRecord (tRow "c" tString tRowNil))
            []

    describe "• Larger expressions" $ do

        -- fix loopList =
        --   (g, ys) =>
        --     match ys with
        --       | [x :: xs]  => g(Cons'(x, xs, loopList(g, xs)))
        --       | [[]]       => g(Nil')
        --   in
        --     let length(xs) =
        --       xs.loopList(fun
        --         | [Cons'(_, _, a)]
        --                    => 1 + a
        --         | [Nil']     => 0 : int)
        --       in
        --         let xs = [2] : List int
        --           in
        --             match xs with
        --               | [x :: _]
        --                   when(length(xs) <= 3) => x
        --               | [_]                     => 0
        --
        succeedInferExpr
            (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TBig 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TBig 2)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Choice [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TBig 3))] (varExpr () "x")] , Clause () (anyPat ()) [Choice [] (litExpr () (TBig 0))] ]))))
            tInt
            []

        -- let
        --   r =
        --     { z = 1 : Int }
        --   in
        --     { a = 1 : Int
        --     , b = 2 : Int
        --     , d = 3 : Int
        --     | r }
        --
        succeedInferExpr
            (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TBig 1))) (conExpr () "{}" []))) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TBig 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TBig 3))) (varExpr () "r"))))))
            (tRecord (tRow "a" tInt (tRow "b" tInt (tRow "d" tInt (tRow "z" tInt (tCon kRow "{}"))))))
            []

        -- ((x, y) =>
        --   match (x, y) with
        --     | [(1 : Int, x)]
        --         when(x /= 0) => x
        --         otherwise    => 0 : int
        --     | [_]            => 100 : int)(1, 5)
        --
        succeedInferExpr
            (appExpr () [ lamExpr () [varPat () "x", varPat () "y"] (patExpr () (tupleExpr () [varExpr () "x", varExpr () "y"]) [ Clause () (tuplePat () [annPat tInt (litPat () (TBig 1)), varPat () "x"])  [ Choice [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TBig 0))] (varExpr () "x") , Choice [] (annExpr tInt (litExpr () (TBig 0))) ] , Clause () (anyPat ()) [ Choice [] (annExpr tInt (litExpr () (TBig 100))) ] ]) , litExpr () (TBig 1) , litExpr () (TBig 5) ])
            tInt
            []

        succeedInferExpr
            (appExpr () [appExpr () [varExpr () "(+)", annExpr tInt (litExpr () (TBig 5))], litExpr () (TBig 5)])
            tInt
            []

        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (op2Expr () (OSub ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "pred")) (appExpr () [varExpr () "f", holeExpr (), annExpr tInt (litExpr () (TBig 1))]) (appExpr () [varExpr () "pred", litExpr () (TBig 11)])))
            tInt
            []

        succeedInferExpr
            (Fix (EOp2 () (ODot ()) (Fix (EVar () "c")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "b")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "a")) (Fix (ECon () "#" [Fix (ERow () "a" (Fix (ECon () "#" [Fix (ERow () "b" (Fix (ECon () "#" [Fix (ERow () "c" (Fix (ELit () (TString "d"))) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))]))))))))
            tString
            []

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EAnn (Fix (TApp (Fix (KVar "k15")) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KCon "*")))) "List")) (Fix (TCon (Fix (KCon "*")) "int")))) (Fix (EList () [Fix (ELit () (TBig 1))])))) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PCon () "(::)" [Fix (PVar () "x"),Fix (PAny ())]), clauseChoices = [Choice [Fix (EOp2 () (OEq ()) (Fix (EVar () "x")) (Fix (ELit () (TBig 1))))] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
            tInt
            []

        succeedInferExpr
            (letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BFun () "add5" [varPat () "z"]) (appExpr () [varExpr () "add", varExpr () "z", annExpr tInt (litExpr () (TBig 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TBig 3))])))
            tInt
            []

        succeedInferExpr
            (letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "add5")) (appExpr () [varExpr () "add", holeExpr (), annExpr tInt (litExpr () (TBig 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TBig 3))])))
            tInt
            []

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 1)))),Fix (ELit () (TBig 2)),Fix (ELit () (TBig 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
            tInt
            []

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 5)))),Fix (ELit () (TBig 3)),Fix (ELit () (TBig 3)),Fix (ELit () (TBig 3))])) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
            tInt
            []

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 5)))),Fix (ELit () (TBig 3)),Fix (ELit () (TBig 3))])) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]} ]))))
            tInt
            []

        succeedInferExpr
            (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3), litExpr () (TBig 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "map" [varPat () "f", varPat () "ys"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], varExpr () "a"])] , Clause () [conPat () "Nil'" []] [Choice [] (conExpr () "[]" [])] ] ]) (varExpr () "ys")) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , testList ]))))
            (tList tInt)
            []

        succeedInferExpr
            (listExpr () [annExpr tInt (litExpr () (TBig 2)), litExpr () (TBig 3), litExpr () (TBig 4), litExpr () (TBig 5)])
            (tList tInt)
            []

        succeedInferExpr
            (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3), litExpr () (TBig 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] , varExpr () "testList" ])))
            tInt
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TBig 2))]]))
            tInt
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TBig 100))]]))
            tInt
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] ]) (appExpr () [varExpr () "fn", annExpr (tApp kTyp (tCon kFun "Option") tInt) (conExpr () "None" [])]))
            tInt
            []

        succeedInferExpr
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TBig 5))]) (conExpr () "None" [])))
            tInt
            []

        succeedInferExpr
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TBig 5))]) (conExpr () "Some" [annExpr tInt (litExpr () (TBig 3))])))
            tInt
            []

        succeedInferExpr
            (appExpr () [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) , annExpr tInt (litExpr () (TBig 5)) , litExpr () (TBig 3) ])
            tInt
            []

        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TBig 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "foo"), conExpr () "Some" [annExpr tInt (litExpr () (TBig 2))]]))
            tInt
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TBig 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "baz"), conExpr () "Some" [annExpr tInt (litExpr () (TBig 2))]]))
            tInt
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z")))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))
            []

        succeedInferExpr
            (appExpr () [ lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))) , recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])) ])
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))
            []

        succeedInferExpr
            (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))))
            (tArr (tRecord (tVar kRow "a")) (tRecord (tRow "a" tInt (tVar kRow "a"))))
            []

        succeedInferExpr
            (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z") , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" [])) ])
            (tRecord tRowNil)
            []

        succeedInferExpr
            (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z") , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" [])))) ])
            (tRecord (tRow "b" tInt (tRow "d" tInt tRowNil)))
            []

        succeedInferExpr
            (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "c" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" []))))) (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z"), varExpr () "r" ]))
            (tRecord (tRow "b" tInt (tRow "c" tInt tRowNil)))
            []

        --  fix map =
        --    f => fun | [[]] => [] | [x :: xs] => f(x) :: map(f, xs)
        --    in
        --      map(x => x + 1, [1, 2, 3] : List int)
        succeedInferExpr
            (fixExpr () "map" (lamExpr () [varPat () "f"] (funExpr () [ Clause () [conPat () "[]" []] [ Choice [] (conExpr () "[]" []) ] , Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [ Choice [] (conExpr () "(::)" [ appExpr () [varExpr () "f", varExpr () "x"] , appExpr () [varExpr () "map", varExpr () "f", varExpr () "xs"] ]) ]])) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3)]) ]))
            (tList tInt)
            []

        succeedInferExpr
            (fixExpr () "foldsucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldsucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (letExpr () (BFun () "toInt" [varPat () "n"]) (appExpr () [ varExpr () "foldsucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , annExpr tInt (litExpr () (TBig 0)) , varExpr () "n" ]) (appExpr () [ varExpr () "foldsucc" , lamExpr () [varPat () "n", varPat () "x"] (op2Expr () (OMul ()) (appExpr () [varExpr () "toInt", varExpr () "n"]) (varExpr () "x")) , annExpr tInt (litExpr () (TBig 1)) , conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "zero" []]]]]] ])))
            tInt
            []

        succeedInferExpr
            (let testTree = conExpr () "Node" [ annExpr tInt (litExpr () (TBig 5)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 3)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 1)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 4)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 7)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Leaf" [] ] ] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 6)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] ] ] in letExpr () (BPat () (varPat () "testTree")) testTree (fixExpr () "loopTree" (lamExpr () [varPat () "g", varPat () "t"] (patExpr () (varExpr () "t") [ Clause () (conPat () "Node" [varPat () "n", varPat () "t1", varPat () "t2"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Node'" [varExpr () "n", varExpr () "t1", varExpr () "t2", appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t1"], appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t2"]]])] , Clause () (conPat () "Leaf" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Leaf'" []])] ])) (appExpr () [ varExpr () "loopTree" , funExpr () [ Clause () [conPat () "Node'" [varPat () "n", varPat () "t1", varPat () "t2", varPat () "a", varPat () "b"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "n") (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))] , Clause () [conPat () "Leaf'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] , varExpr () "testTree" ])))
            tInt
            []

        succeedInferExpr
            (fixExpr () "foldsucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldsucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (appExpr () [ varExpr () "foldsucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , annExpr tInt (litExpr () (TBig 0)) , conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "zero" []]]] ]))
            tInt
            []

        succeedInferExpr
            (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
            (tRecord tRowNil)
            []

        succeedInferExpr
            (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
            tInt
            []

        -- let r = { a = 1 : Int, b = 2 : int } in r.b
        succeedInferExpr
            (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (op2Expr () (ODot ()) (varExpr () "b") (varExpr () "r")))
            tInt
            []

        -- let f(x) = x + 1 in f(123 : int)
        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))]))
            tInt
            []

        -- ( fun
        --     | (True, Some(true))  => 1 : int
        --     | (True, Some(false)) => 2
        --     | (_, _)              => 3 )(True, Some(false))
        --
        succeedInferExpr
            (appExpr () [ funExpr () [ Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]] [ Choice [] (annExpr tInt (litExpr () (TInt 1))) ] , Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]] [ Choice [] (litExpr () (TInt 2)) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (litExpr () (TInt 3)) ] ] , litExpr () (TBool True) , conExpr () "Some" [litExpr () (TBool False)] ])
            tInt
            []

        -- ( fun
        --     | (True, Some(true))  => 1 : int
        --     | (True, Some(false)) => 2 )(true, Some(false))
        --
        succeedInferExpr
            (appExpr () [ funExpr () [ Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]] [ Choice [] (annExpr tInt (litExpr () (TInt 1))) ] , Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]] [ Choice [] (litExpr () (TInt 2)) ] ] , litExpr () (TBool True) , conExpr () "Some" [litExpr () (TBool False)] ])
            tInt
            [NonExhaustivePatterns]

        succeedInferExpr
            (funExpr () [ Clause () [litPat () (TBool True), litPat () (TBool True)] [Choice [] (litExpr () (TInt 1))] , Clause () [litPat () (TBool False), litPat () (TBool False)] [Choice [] (litExpr () (TInt 2))] , Clause () [varPat () "x", varPat () "y"] [Choice [] (litExpr () (TInt 3))] ])
            _a
            []

        succeedInferExpr
            (funExpr () [ Clause () [litPat () (TBool True), litPat () (TBool True)] [Choice [] (litExpr () (TInt 1))] , Clause () [litPat () (TBool False), litPat () (TBool False)] [Choice [] (litExpr () (TInt 2))] ])
            _a
            [NonExhaustivePatterns]

-------------------------------------------------------------------------------

-- Prettyprinters tests

suceedPrint :: (Pretty p) => p -> Text -> SpecWith ()
suceedPrint p str =
    describe output $
        it "✔ OK" $
            output == str
  where
    output = prettyT p

suceedPrintType :: Type -> Text -> SpecWith ()
suceedPrintType = suceedPrint

suceedPrintPattern :: ProgPattern t Void -> Text -> SpecWith ()
suceedPrintPattern = suceedPrint

suceedPrintExpr :: ProgExpr t Void -> Text -> SpecWith ()
suceedPrintExpr = suceedPrint

suceedPrintTypedecl :: Typedecl -> Text -> SpecWith ()
suceedPrintTypedecl = suceedPrint

suceedPrintExprW :: Int -> ProgExpr t Void -> Text -> SpecWith ()
suceedPrintExprW w expr str =
    describe output $
        it "✔ OK" $
            output == str
  where
    output = prettyW w expr

testPrettyprinters :: SpecWith ()
testPrettyprinters = do

    describe "• Prim" $ do

        suceedPrint
            TUnit
            "()"

        suceedPrint
            (TString "klingon")
            "\"klingon\""

        suceedPrint
            (TChar 'a')
            "'a'"

        suceedPrint
            (TFloat 3.14)
            "3.14"

    describe "• Type" $ do

        suceedPrintType
            (_a `tArr` _b)
            "a -> b"

        suceedPrintType
            tInt
            "int"

        suceedPrintType
            (_a `tArr` _b `tArr` _c)
            "a -> b -> c"

        suceedPrintType
            ((_a `tArr` _b) `tArr` _c)
            "(a -> b) -> c"

        suceedPrintType
            (tList tInt `tArr` _b `tArr` _c)
            "List int -> b -> c"

        suceedPrintType
            (tList (tList tInt))
            "List (List int)"

        suceedPrintType
            (tList (tInt `tArr` _a))
            "List (int -> a)"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") tInt) tInt)
            "C int int"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") tInt) tInt `tArr` _a)
            "C int int -> a"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) tInt `tArr` _a)
            "C (a -> a) int -> a"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) (_b `tArr` _b) `tArr` _a)
            "C (a -> a) (b -> b) -> a"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) (tApp kTyp (tCon kFun "D") _b) `tArr` _a)
            "C (a -> a) (D b) -> a"

        suceedPrintType
            (tRecord (tRow "id" _a (tRow "name" _b (tVar kRow "r"))))
            "{ id : a, name : b | r }"

        suceedPrintType
            (tRecord (tRow "id" _a (tRow "name" _b tRowNil)))
            "{ id : a, name : b }"

        suceedPrintType
            (tRecord tRowNil)
            "{}"

        suceedPrintType
            (tApp kTyp (tApp kTyp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tCon kTyp "string")) (tCon kTyp "bool"))
            "(string, bool)"

    describe "• Kind" $ do

        suceedPrint
            kRow
            "Row"

        suceedPrint
            (kTyp `kArr` kTyp)
            "* -> *"

        suceedPrint
            (kTyp `kArr` kTyp `kArr` kTyp)
            "* -> * -> *"

        suceedPrint
            ((kTyp `kArr` kTyp) `kArr` kTyp)
            "(* -> *) -> *"

    describe "• Pattern" $ do

        suceedPrintPattern
            (varPat () "v")
            "v"

        suceedPrintPattern
            (anyPat ())
            "_"

        suceedPrintPattern
            (litPat () (TInt 5))
            "5"

        suceedPrintPattern
            (orPat () (varPat () "v") (litPat () (TInt 5)))
            "v or 5"

        suceedPrintPattern
            (asPat () "five" (litPat () (TInt 5)))
            "5 as five"

        suceedPrintPattern
            (tuplePat () [varPat () "x", varPat () "y"])
            "(x, y)"

        suceedPrintPattern
            (tuplePat () [varPat () "x", anyPat ()])
            "(x, _)"

        suceedPrintPattern
            (listPat () [varPat () "x", anyPat ()])
            "[x, _]"

        suceedPrintPattern
            (listPat () [])
            "[]"

        suceedPrintPattern
            (litPat () TUnit)
            "()"

        suceedPrintPattern
            (recordPat () (rowPat () "id" (varPat () "id") (rowPat () "name" (varPat () "name") (conPat () "{}" []))))
            "{ id = id, name = name }"

        describe "• Constructor patterns" $ do

            suceedPrintPattern
                (conPat () "C" [])
                "C"

            suceedPrintPattern
                (conPat () "C" [varPat () "x", varPat () "y"])
                "C(x, y)"

            suceedPrintPattern
                (conPat () "C" [varPat () "x", conPat () "D" [varPat () "y", varPat () "z"]])
                "C(x, D(y, z))"

            suceedPrintPattern
                (conPat () "C" [varPat () "x", conPat () "D" []])
                "C(x, D)"

            suceedPrintPattern
                (conPat () "C" [orPat () (varPat () "x") (varPat () "y")])
                "C(x or y)"

            suceedPrintPattern
                (conPat () "C" [varPat () "x", asPat () "d" (conPat () "D" [varPat () "y"])])
                "C(x, D(y) as d)"

            describe "• List constructor patterns" $ do

                suceedPrintPattern
                    (conPat () "(::)" [varPat () "x", varPat () "xs"])
                    "x :: xs"

    describe "• Predicates" $ do

        suceedPrint
            (InClass "Show" _a)
            "Show a"

        suceedPrint
            (InClass "Eq" tInt :: Predicate)
            "Eq int"

    describe "• Expr" $ do

        suceedPrintExpr
            (appExpr () [varExpr () "add", litExpr () (TBig 3), holeExpr ()])
            "add(3, _)"

        suceedPrintExpr
            (tupleExpr () [varExpr () "x", litExpr () (TInt 5)])
            "(x, 5)"

        suceedPrintExprW 10
            (tupleExpr () [varExpr () "z", varExpr () "y", varExpr () "x", litExpr () (TInt 5)])
            "( z\n, y\n, x\n, 5 )"

        suceedPrintExpr
            (recordExpr () (rowExpr () "id" (varExpr () "id") (rowExpr () "name" (varExpr () "name") (conExpr () "{}" []))))
            "{ id = id, name = name }"

--        suceedPrintExprW 10
--            (recordExpr () (rowExpr () "id" (varExpr () "id") (rowExpr () "name" (varExpr () "name") (conExpr () "{}" []))))
--            "{ id = id\n, name = name\n }"

        describe "• Typedecl expressions" $ do

            suceedPrintExpr
                (conExpr () "C" [])
                "C"

            suceedPrintExpr
                (conExpr () "C" [varExpr () "x", varExpr () "y"])
                "C(x, y)"

            suceedPrintExpr
                (conExpr () "C" [varExpr () "x", conExpr () "D" [varExpr () "y", varExpr () "z"]])
                "C(x, D(y, z))"

            suceedPrintExpr
                (conExpr () "C" [varExpr () "x", conExpr () "D" []])
                "C(x, D)"

            describe "• List constructor" $ do

                suceedPrintExpr
                    (conExpr () "(::)" [varExpr () "x", varExpr () "xs"])
                    "x :: xs"

        describe "• Records" $ do

            suceedPrintExpr
                (recordExpr () (conExpr () "{}" []))
                "{}"

        describe "• Type declarations" $ do

            suceedPrintTypedecl
                (Sum "List" ["a"] [Mul "A" [Fix (TCon (Fix (KCon "*")) "int"),Fix (TCon (Fix (KCon "*")) "bool")]])
                "type List a = A int bool"

-------------------------------------------------------------------------------

-- Flight tests

succeedRunExpr :: ProgExpr () Type -> Maybe (Value Eval) -> SpecWith ()
succeedRunExpr expr result =
    describe (prettyT expr) $ do
        it ("✔ evaluates to " <> prettyT (show result)) $
            result == j
  where
    (a, (_, _, ctx)) = runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType expr)

    c :: ProgExpr TInfo Void
    c = runReader (exhaustivePatternsCheck (astExpr a)) testConstructorEnv

    (c1, _) = runSupplyNats (runReaderT (ambiguityCheck ctx c) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))
    c2 = normalizeExpr c1

    d = stage1Translate c2

    e = runSupplyNats (runReaderT (stage2Translate d) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv))

    f = translateLiteral e

    g = runSupplyNats (runReaderT (evalStateT (stage3Translate f) mempty) (mempty, (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv)))

    h = runSupplyNats (stage4Translate g)

    i = coreTranslate h

    j = evalExpr i testEvalEnv

--    describe ("The inferred type of the expression " <> prettyT expr) $ do
--        it ("✔ is unifiable with " <> prettyT ty) $
--            isRight res
--        if null errs
--            then
--                it "✔ contains no errors" $
--                    not (hasErrors e1)
--            else
--                it ("✔ contains errors: " <> pack (show errs)) $
--                    and [err `elem` allErrors e1 | err <- errs]
--  where
--    (Ast e, (typeSub, kindSub, context)) =
--        runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType (Ast expr))
--
--    res = runMatch ty (typeOf (applyBoth (typeSub, kindSub) e))
--    e1  = runReader (exhaustivePatternsCheck e) testConstructorEnv

testFlight :: SpecWith ()
testFlight = do

    succeedRunExpr
        (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TBig 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TBig 2)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Choice [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TBig 3))] (varExpr () "x")] , Clause () (anyPat ()) [Choice [] (litExpr () (TBig 0))] ]))))
        (Just (Value (TInt 2)))

    succeedRunExpr
        (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TBig 1))) (conExpr () "{}" []))) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TBig 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TBig 3))) (appExpr () [varExpr () "_#", varExpr () "r"]))))))
        (Just (Data "#" [Data "{a}" [Value (TInt 1), Data "{b}" [Value (TInt 2), Data "{d}" [Value (TInt 3), Data "{z}" [Value (TInt 1), Data "{}" []]]]]]))

    succeedRunExpr
        (appExpr () [ lamExpr () [varPat () "x", varPat () "y"] (patExpr () (tupleExpr () [varExpr () "x", varExpr () "y"]) [ Clause () (tuplePat () [annPat tInt (litPat () (TBig 1)), varPat () "x"])  [ Choice [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TBig 0))] (varExpr () "x") , Choice [] (annExpr tInt (litExpr () (TBig 0))) ] , Clause () (anyPat ()) [ Choice [] (annExpr tInt (litExpr () (TBig 100))) ] ]) , litExpr () (TBig 1) , litExpr () (TBig 5) ])
        (Just (Value (TInt 5)))

    succeedRunExpr
        (appExpr () [appExpr () [varExpr () "(+)", annExpr tInt (litExpr () (TBig 5))], litExpr () (TBig 5)])
        (Just (Value (TInt 10)))

    succeedRunExpr
        (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (op2Expr () (OSub ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "pred")) (appExpr () [varExpr () "f", holeExpr (), annExpr tInt (litExpr () (TBig 1))]) (appExpr () [varExpr () "pred", litExpr () (TBig 11)])))
        (Just (Value (TInt 10)))

    succeedRunExpr
        (Fix (EOp2 () (ODot ()) (Fix (EVar () "c")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "b")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "a")) (Fix (ECon () "#" [Fix (ERow () "a" (Fix (ECon () "#" [Fix (ERow () "b" (Fix (ECon () "#" [Fix (ERow () "c" (Fix (ELit () (TString "d"))) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))]))))))))
        (Just (Value (TString "d")))

    succeedRunExpr
        (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EAnn (Fix (TApp (Fix (KVar "k15")) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KCon "*")))) "List")) (Fix (TCon (Fix (KCon "*")) "int")))) (Fix (EList () [Fix (ELit () (TBig 1))])))) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PCon () "(::)" [Fix (PVar () "x"),Fix (PAny ())]), clauseChoices = [Choice [Fix (EOp2 () (OEq ()) (Fix (EVar () "x")) (Fix (ELit () (TBig 1))))] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
        (Just (Value (TInt 1)))

    succeedRunExpr
        (letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BFun () "add5" [varPat () "z"]) (appExpr () [varExpr () "add", varExpr () "z", annExpr tInt (litExpr () (TBig 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TBig 3))])))
        (Just (Value (TInt 8)))

    succeedRunExpr
        (letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "add5")) (appExpr () [varExpr () "add", holeExpr (), annExpr tInt (litExpr () (TBig 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TBig 3))])))
        (Just (Value (TInt 8)))

    succeedRunExpr
        (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 1)))),Fix (ELit () (TBig 2)),Fix (ELit () (TBig 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
        (Just (Value (TInt 1)))

    succeedRunExpr
        (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 100)))),Fix (ELit () (TBig 2)),Fix (ELit () (TBig 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
        (Just (Value (TInt 100)))

    succeedRunExpr
        (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 100))))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
        (Just (Value (TInt 100)))

    succeedRunExpr
        (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 100)))),Fix (ELit () (TBig 2)),Fix (ELit () (TBig 3)),Fix (ELit () (TBig 4))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
        (Just (Value (TInt 0)))

    succeedRunExpr
        (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "int")) (Fix (ELit () (TBig 5)))),Fix (ELit () (TBig 3)),Fix (ELit () (TBig 3)),Fix (ELit () (TBig 3))])) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TBig 0)))]}]))))
        (Just (Value (TInt 0)))

    succeedRunExpr
        (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3), litExpr () (TBig 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "map" [varPat () "f", varPat () "ys"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], varExpr () "a"])] , Clause () [conPat () "Nil'" []] [Choice [] (conExpr () "[]" [])] ] ]) (varExpr () "ys")) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , testList ]))))
        (Just (Data "(::)" [Value (TInt 2), Data "(::)" [Value (TInt 3), Data "(::)" [Value (TInt 4), Data "(::)" [Value (TInt 5), Data "[]" []]]]]))

    succeedRunExpr
        (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3), litExpr () (TBig 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] , varExpr () "testList" ])))
        (Just (Value (TInt 10)))

    succeedRunExpr
        (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TBig 2))]]))
        (Just (Value (TInt 2)))

    succeedRunExpr
        (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] ]) (appExpr () [varExpr () "fn", annExpr (tApp kTyp (tCon kFun "Option") tInt) (conExpr () "None" [])]))
        (Just (Value (TInt 0)))

    succeedRunExpr
        (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TBig 5))]) (conExpr () "None" [])))
        (Just (Value (TInt 5)))

    succeedRunExpr
        (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TBig 5))]) (conExpr () "Some" [annExpr tInt (litExpr () (TBig 3))])))
        (Just (Value (TInt 3)))

    succeedRunExpr
        (appExpr () [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) , annExpr tInt (litExpr () (TBig 5)) , litExpr () (TBig 3) ])
        (Just (Value (TInt 8)))

    succeedRunExpr
        (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TBig 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "foo"), conExpr () "Some" [annExpr tInt (litExpr () (TBig 2))]]))
        (Just (Value (TInt 2)))

    succeedRunExpr
        (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 1))] (litExpr () (TBig 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TBig 2))] (litExpr () (TBig 2)) , Choice [] (litExpr () (TBig 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TBig 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TBig 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "baz"), conExpr () "Some" [annExpr tInt (litExpr () (TBig 2))]]))
        (Just (Value (TInt 999)))

    succeedRunExpr
        (fixExpr () "map" (lamExpr () [varPat () "f"] (funExpr () [ Clause () [conPat () "[]" []] [ Choice [] (conExpr () "[]" []) ] , Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [ Choice [] (conExpr () "(::)" [ appExpr () [varExpr () "f", varExpr () "x"] , appExpr () [varExpr () "map", varExpr () "f", varExpr () "xs"] ]) ]])) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3)]) ]))
        (Just (Data "(::)" [Value (TInt 2), Data "(::)" [Value (TInt 3), Data "(::)" [Value (TInt 4), Data "[]" []]]]))

    succeedRunExpr
        (fixExpr () "foldsucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldsucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (letExpr () (BFun () "toInt" [varPat () "n"]) (appExpr () [ varExpr () "foldsucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , annExpr tInt (litExpr () (TBig 0)) , varExpr () "n" ]) (appExpr () [ varExpr () "foldsucc" , lamExpr () [varPat () "n", varPat () "x"] (op2Expr () (OMul ()) (appExpr () [varExpr () "toInt", varExpr () "n"]) (varExpr () "x")) , annExpr tInt (litExpr () (TBig 1)) , conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "zero" []]]]]] ])))
        (Just (Value (TInt 120)))

    succeedRunExpr
        (let testTree = conExpr () "Node" [ annExpr tInt (litExpr () (TBig 5)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 3)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 1)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 4)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 7)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Leaf" [] ] ] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 6)) , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TBig 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] ] ] in letExpr () (BPat () (varPat () "testTree")) testTree (fixExpr () "loopTree" (lamExpr () [varPat () "g", varPat () "t"] (patExpr () (varExpr () "t") [ Clause () (conPat () "Node" [varPat () "n", varPat () "t1", varPat () "t2"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Node'" [varExpr () "n", varExpr () "t1", varExpr () "t2", appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t1"], appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t2"]]])] , Clause () (conPat () "Leaf" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Leaf'" []])] ])) (appExpr () [ varExpr () "loopTree" , funExpr () [ Clause () [conPat () "Node'" [varPat () "n", varPat () "t1", varPat () "t2", varPat () "a", varPat () "b"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "n") (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))] , Clause () [conPat () "Leaf'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] , varExpr () "testTree" ])))
        (Just (Value (TInt 46)))

    succeedRunExpr
        (fixExpr () "foldsucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldsucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (appExpr () [ varExpr () "foldsucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) , annExpr tInt (litExpr () (TBig 0)) , conExpr () "succ" [conExpr () "succ" [conExpr () "succ" [conExpr () "zero" []]]] ]))
        (Just (Value (TInt 3)))

    succeedRunExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))]))
        (Just (Value (TInt 124)))

    succeedRunExpr
        (appExpr () [ funExpr () [ Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]] [ Choice [] (annExpr tInt (litExpr () (TInt 1))) ] , Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]] [ Choice [] (litExpr () (TInt 2)) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (litExpr () (TInt 3)) ] ] , litExpr () (TBool True) , conExpr () "Some" [litExpr () (TBool False)] ])
        (Just (Value (TInt 2)))

    succeedRunExpr
        (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
        (Just (Value (TInt 5)))

    succeedRunExpr
        (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
        (Just (Data "#" [Data "{a}" [Value (TInt 1), Data "{b}" [Value (TInt 2), Data "{}" []]]]))

    succeedRunExpr
        (appExpr () [lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TBig 1))) (varExpr () "z"))), recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])
        (Just (Data "#" [Data "{a}" [Value (TInt 1), Data "{b}" [Value (TInt 2), Data "{}" []]]]))

    succeedRunExpr
        (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z") , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" [])))) ])
        (Just (Data "#" [Data "{b}" [Value (TInt 2), Data "{d}" [Value (TInt 3), Data "{}" []]]]))

    succeedRunExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OGt ()) (varExpr () "x") (litExpr () (TBig 6))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TBig 4))]))
        (Just (Value (TBool False)))

    succeedRunExpr
        (letExpr () (BPat () (varPat () "foo")) (funExpr ()
            [ Clause () [litPat () (TBig 0)] [Choice [] (annExpr tInt (litExpr () (TBig 1)))]
            , Clause () [varPat () "n"] [Choice [] (annExpr tInt (litExpr () (TBig 2)))]
            ]) (appExpr () [varExpr () "foo", annExpr tInt (litExpr () (TBig 1))]))
        (Just (Value (TInt 2)))

    succeedRunExpr
        (op2Expr () (OPow ()) (annExpr tDouble (litExpr () (TDouble 5.0))) (annExpr tInt (litExpr () (TBig 3))))
        (Just (Value (TDouble 125.0)))

    succeedRunExpr
        (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TBig 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TBig 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2)])) (appExpr () [varExpr () "length", varExpr () "xs"]))))
        (Just (Value (TInt 2)))

    succeedRunExpr
        (fixExpr () "nat'"
            (lamExpr () [varPat () "go", varPat () "n"]
                (patExpr () (varExpr () "n")
                  [ Clause () (conPat () "succ" [varPat () "m"]) [Choice [] (appExpr () [varExpr () "go", conExpr () "succ'" [varExpr () "m", appExpr () [varExpr () "nat'", varExpr () "go", varExpr () "m"]]])]
                  , Clause () (conPat () "zero" []) [Choice [] (appExpr () [varExpr () "go", conExpr () "zero'" []])] ]))
          (letExpr ()
              (BFun () "factorial" [varPat () "n"])
              (appExpr () [varExpr () "nat'", funExpr ()
                  [ Clause () [conPat () "zero'" []] [Choice [] (conExpr () "succ" [conExpr () "zero" []])]
                  , Clause () [conPat () "succ'" [varPat () "m", varPat () "x"]] [Choice [] (op2Expr () (OMul ()) (conExpr () "succ" [varExpr () "m"]) (varExpr () "x"))]
                  ], varExpr () "n"])
              (appExpr () [varExpr () "factorial", litExpr () (TBig 4)])))
        (Just (fromJust (evalExpr (cApp [cVar ";pack", cLit (TBig 24)]) testEvalEnv)))

--        (fixExpr () "f"
--            (funExpr () [ Clause () [litPat () (TBig 0)] [Choice [] (conExpr () "zero" [])]
--                        , Clause () [varPat () "n"] [Choice [] (conExpr () "succ" [appExpr () [varExpr () "f", op2Expr () (OSub ()) (varExpr () "n") (litExpr () (TBig 1))]])] ])
--        (varExpr () "f")

    succeedRunExpr
        (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (litExpr () (TBig 0)))
        (Just (Value (TNat 0)))

    succeedRunExpr
        (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (conExpr () "zero" []))
        (Just (Value (TNat 0)))

    succeedRunExpr
        (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (conExpr () "succ" [conExpr () "zero" []]))
        (Just (Value (TNat 9)))

    succeedRunExpr
        (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (conExpr () "succ" [litExpr () (TBig 0)]))
        (Just (Value (TNat 9)))

    succeedRunExpr
        (annExpr tNat (op2Expr () (OSub ()) (litExpr () (TBig 0)) (litExpr () (TBig 100))))
        (Just (Value (TNat 0)))

    succeedRunExpr
        (annExpr tNat (op2Expr () (OSub ()) (conExpr () "zero" []) (litExpr () (TBig 100))))
        (Just (Value (TNat 0)))

    succeedRunExpr
        (appExpr () [funExpr () [ Clause () [annPat tInt (litPat () (TBig 5)), annPat tInt (varPat () "y")] [Choice [] (varExpr () "y")] , Clause () [anyPat (), anyPat ()] [Choice [] (litExpr () (TBig 9))] ], litExpr () (TBig 3), litExpr () (TBig 8) ])
        (Just (Value (TInt 9)))

    succeedRunExpr
        (appExpr () [funExpr () [ Clause () [annPat tInt (litPat () (TBig 5)), annPat tInt (varPat () "y")] [Choice [] (varExpr () "y")] , Clause () [anyPat ()] [Choice [] (litExpr () (TBig 9))] ], litExpr () (TBig 3), litExpr () (TBig 8) ])
        (Just (Value (TInt 9)))

    succeedRunExpr
        (appExpr () [funExpr () [ Clause () [annPat tInt (litPat () (TBig 5)), annPat tInt (varPat () "y")] [Choice [] (varExpr () "y")] , Clause () [anyPat ()] [Choice [] (litExpr () (TBig 9))] ], litExpr () (TBig 5), litExpr () (TBig 8) ])
        (Just (Value (TInt 8)))

    describe "• Defaulting" $ do

        succeedRunExpr
            (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OGt ()) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))) (litExpr () (TBig 5))) (appExpr () [varExpr () "f", litExpr () (TBig 5)]))
            (Just (Value (TBool True)))

        succeedRunExpr
            (letExpr () (BPat () (varPat () "f")) (funExpr ()
                [ Clause () [litPat () (TDouble 0.0)] [Choice [] (annExpr tInt (litExpr () (TBig 1)))]
                , Clause () [varPat () "n"] [Choice [] (annExpr tInt (litExpr () (TBig 2)))]
                ]) (appExpr () [varExpr () "f", litExpr () (TBig 1)]))
            (Just (Value (TInt 2)))

-------------------------------------------------------------------------------

-- Parser tests

succeedParseType :: Parser Type -> Text -> Type -> SpecWith ()
succeedParseType parser input expected =
    describe input $
        it ("✔ parses to " <> prettyT expected) $
            isRight $ do
                result <- runParserStack parser "" input
                pure (runUnify result expected)

succeedParse :: (Pretty a, Eq a) => Parser a -> Text -> a -> SpecWith ()
succeedParse parser input expected =
    describe input $
        it ("✔ parses to " <> prettyT expected) $
            result == expected
  where
    Right result = runParserStack parser "" input

failParse :: (Eq a) => Parser a -> Text -> SpecWith ()
failParse parser input =
    describe input $
        it "✗ fails to parse" $
            isLeft (runParserStack parser "" input)

testParse :: SpecWith ()
testParse = do

    describe "• Typedecl" $ do

        succeedParse typedeclParser
            "type List a = Nil | Cons a (List a)"
            (Sum "List" ["a"] [ Mul "Nil" [] , Mul "Cons" [tVar kTyp "a", tApp kTyp (tCon kFun "List") (tVar kTyp "a")]])

        succeedParse typeParser
            "{ name : string }"
            (tRecord (tRow "name" tString tRowNil))

        succeedParse typedeclParser
            "type User = User { name : string }"
            (Sum "User" [] [ Mul "User" [ tRecord (tRow "name" tString tRowNil) ] ])

        succeedParse typedeclParser
            "type User a = User { name : string | a }"
            (Sum "User" ["a"] [ Mul "User" [ tRecord (tRow "name" tString (tVar kRow "a")) ] ])

    describe "• Prim" $ do

        succeedParse primParser
            "5"
            (TBig 5)

        succeedParse primParser
            "5.3"
            (TDouble 5.3)

        succeedParse primParser
            "true"
            (TBool True)

        succeedParse primParser
            "'x'"
            (TChar 'x')

        succeedParse primParser
            "\"klingon\""
            (TString "klingon")

    describe "• Type" $ do

        succeedParseType typeParser
            "int"
            tInt

        succeedParseType typeParser
            "int -> int"
            (tInt `tArr` tInt)

        succeedParseType typeParser
            "List int"
            (tList tInt)

        succeedParseType typeParser
            "List (List int)"
            (tApp kTyp (tCon (kArr kTyp kTyp) "List") (tApp kTyp (tCon (kArr kTyp kTyp) "List") tInt))

        succeedParseType typeParser
            "List a"
            (tApp kTyp (tCon (kArr kTyp kTyp) "List") (tVar kTyp "a"))

        succeedParseType typeParser
            "m a"
            (tApp kTyp (tVar (kArr kTyp kTyp) "m") (tVar kTyp "a"))

        succeedParseType typeParser
            "List int -> a"
            (tApp kTyp (tCon (kArr kTyp kTyp) "List") tInt `tArr` tVar kTyp "a")

        succeedParseType typeParser
            "A B C"
            (tApp kTyp (tApp (kArr kTyp kTyp) (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tCon kTyp "B")) (tCon kTyp "C") :: Type)

        succeedParseType typeParser
            "A b c"
            (tApp kTyp (tApp (kArr kTyp kTyp) (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tVar kTyp "b")) (tVar kTyp "c") :: Type)

        succeedParseType typeParser
            "A (B C) D"
            (tApp kTyp (tApp (kArr kTyp kTyp) (tCon (kArr kTyp (kArr kTyp kTyp)) "A") (tApp kTyp (tCon (kArr kTyp kTyp) "B") (tCon kTyp "C"))) (tCon kTyp "D") :: Type)

        describe "• Tuples" $ do

            succeedParseType typeParser
                "(int, int)"
                (tTuple [tInt, tInt])

            succeedParseType typeParser
                "(int, a)"
                (tTuple [tInt, tVar kTyp "a"])

        describe "• Records" $ do

            succeedParseType typeParser
                "{ a : int }"
                (tRecord (tRow "a" tInt tRowNil))

            succeedParseType typeParser
                "{ a : int, b : a }"
                (tRecord (tRow "a" tInt (tRow "b" (tVar kTyp "a") tRowNil)))

            succeedParseType typeParser
                "{ a : int, b : a | c }"
                (tRecord (tRow "a" tInt (tRow "b" (tVar kTyp "a") (tVar kRow "c"))))

            succeedParseType typeParser
                "{}"
                (tRecord tRowNil)

    describe "• Pattern" $ do

        succeedParse annPatternParser
            "x"
            (varPat () "x")

        succeedParse annPatternParser
            "5"
            (litPat () (TBig 5))

        succeedParse annPatternParser
            "Some(x)"
            (conPat () "Some" [varPat () "x"])

        succeedParse annPatternParser
            "None"
            (conPat () "None" [])

        succeedParse annPatternParser
            "_"
            (anyPat ())

        succeedParse annPatternParser
            "(4, 3)"
            (tuplePat () [litPat () (TBig 4), litPat () (TBig 3)])

        succeedParse annPatternParser
            "x or 5"
            (orPat () (varPat () "x") (litPat () (TBig 5)))

        succeedParse annPatternParser
            "{ x = 5 }"
            (recordPat () (rowPat () "x" (litPat () (TBig 5)) (conPat () "{}" [])))

        succeedParse annPatternParser
            "{ x = 5 } as y"
            (asPat () "y" (recordPat () (rowPat () "x" (litPat () (TBig 5)) (conPat () "{}" []))))

        succeedParse annPatternParser
            "{}"
            (recordPat () (conPat () "{}" []))

        succeedParse annPatternParser
            "[1, 2]"
            (listPat () [litPat () (TBig 1), litPat () (TBig 2)])

        succeedParse annPatternParser
            "[]"
            (conPat () "[]" [])

        succeedParse annPatternParser
            "x : int"
            (annPat tInt (varPat () "x"))

        succeedParse annPatternParser
            "5 : int"
            (annPat tInt (litPat () (TBig 5)))

        succeedParse annPatternParser
            "_ : int"
            (annPat tInt (anyPat ()))

        succeedParse annPatternParser
            "(4, 3) : int"
            (annPat tInt (tuplePat () [litPat () (TBig 4), litPat () (TBig 3)]))

        succeedParse annPatternParser
            "(x or 5) : int"
            (annPat tInt (orPat () (varPat () "x") (litPat () (TBig 5))))

        succeedParse annPatternParser
            "x or 5 : int"
            (annPat tInt (orPat () (varPat () "x") (litPat () (TBig 5))))

        succeedParse annPatternParser
            "(x or 5 : int)"
            (annPat tInt (orPat () (varPat () "x") (litPat () (TBig 5))))

        succeedParse annPatternParser
            "((x or 5 : int))"
            (annPat tInt (orPat () (varPat () "x") (litPat () (TBig 5))))

        succeedParse annPatternParser
            "_ as x : int"
            (annPat tInt (asPat () "x" (anyPat ())))

        succeedParse annPatternParser
            "((_ as x : int))"
            (annPat tInt (asPat () "x" (anyPat ())))

    describe "• Expr" $ do

        succeedParse annExprParser
            "x"
            (varExpr () "x")

        succeedParse annExprParser
            "Some(x)"
            (conExpr () "Some" [varExpr () "x"])

        succeedParse annExprParser
            "None"
            (conExpr () "None" [])

        succeedParse annExprParser
            "(4, 3)"
            (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])

        succeedParse annExprParser
            "((4, 3))"
            (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])

        succeedParse annExprParser
            "(((4, 3)))"
            (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])

        succeedParse annExprParser
            "((((4, 3))))"
            (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])

        succeedParse annExprParser
            "(1, 3, 4)"
            (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "if (4, 3) then (1, 3, 4) else (5, 6, 7)"
            (ifExpr ()
                (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])
                (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 3), litExpr () (TBig 4)])
                (tupleExpr () [litExpr () (TBig 5), litExpr () (TBig 6), litExpr () (TBig 7)]))

        succeedParse annExprParser
            "fn(1, 3, 4)"
            (appExpr () [varExpr () "fn", litExpr () (TBig 1), litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "fn (1, 3, 4)"
            (appExpr () [varExpr () "fn", litExpr () (TBig 1), litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "fn(x, 3, 4)"
            (appExpr () [varExpr () "fn", varExpr () "x", litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "(fn)(x, 3, 4)"
            (appExpr () [varExpr () "fn", varExpr () "x", litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "(fn(x))(y)"
            (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

        succeedParse annExprParser
            "((fn(x))(y))"
            (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

        succeedParse annExprParser
            "[1,2,3]"
            (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2), litExpr () (TBig 3)])

        succeedParse annExprParser
            "let x = (1, 2) in z"
            (letExpr () (BPat () (varPat () "x")) (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 2)]) (varExpr () "z"))

        succeedParse annExprParser
            "let f(x) = (1, 2) in z"
            (letExpr () (BFun () "f" [varPat () "x"]) (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 2)]) (varExpr () "z"))

        succeedParse annExprParser
            "{ x = 5 }"
            (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" [])))

        succeedParse annExprParser
            "{ x = { y = 5 } }"
            (recordExpr () (rowExpr () "x" (recordExpr () (rowExpr () "y" (litExpr () (TBig 5)) (conExpr () "{}" []))) (conExpr () "{}" [])))

        succeedParse annExprParser
            "(x) => x"
            (lamExpr () [varPat () "x"] (varExpr () "x"))

        succeedParse annExprParser
            "x => x"
            (lamExpr () [varPat () "x"] (varExpr () "x"))

        succeedParse annExprParser
            "(x) => { x = 5 }"
            (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" []))))

        succeedParse annExprParser
            "x => { x = 5 }"
            (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" []))))

        succeedParse annExprParser
            "(x => { x = 5 })"
            (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" []))))

        succeedParse annExprParser
            "((x => { x = 5 }))"
            (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" []))))

        succeedParse annExprParser
            "((x) => { x = 5 })"
            (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" []))))

        succeedParse annExprParser
            "((x) => ({ x = 5 }))"
            (lamExpr () [varPat () "x"] (recordExpr () (rowExpr () "x" (litExpr () (TBig 5)) (conExpr () "{}" []))))

        succeedParse annExprParser
            "(x) => x + 1"
            (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))))

        succeedParse annExprParser
            "((x) => x + 1)(5)"
            (appExpr ()
                [ lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1)))
                , litExpr () (TBig 5) ])

        succeedParse annExprParser
            "Some(x) => x + 1"
            (lamExpr () [conPat () "Some" [varPat () "x"]] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))))

        succeedParse annExprParser
            "(Some(x) => x + 1)"
            (lamExpr () [conPat () "Some" [varPat () "x"]] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))))

        succeedParse annExprParser
            "() => ()"
            (lamExpr () [litPat () TUnit] (litExpr () TUnit))

        succeedParse annExprParser
            "let f = (x) => x + 1 in y"
            (letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1)))) (varExpr () "y"))

        succeedParse annExprParser
            "let f = x => x + 1 in y"
            (letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1)))) (varExpr () "y"))

        succeedParse annExprParser
            "let withDefault | Some(y) => y | None => 0 in Some(3)"
            (letExpr () (BPat () (varPat () "withDefault")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [Choice [] (varExpr () "y")] , Clause () [conPat () "None" []] [Choice [] (litExpr () (TBig 0))] ]) (conExpr () "Some" [litExpr () (TBig 3)]))

        succeedParse annExprParser
            "let withDefault(val) | Some(y) => y | None => val in Some(3)"
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [Choice [] (varExpr () "y")] , Clause () [conPat () "None" []] [Choice [] (varExpr () "val")] ]) (conExpr () "Some" [litExpr () (TBig 3)]))

        succeedParse annExprParser
            "{ a = true | b }"
            (recordExpr () (rowExpr () "a" (litExpr () (TBool True)) (varExpr () "b")))

        succeedParse annExprParser
            "{}"
            (recordExpr () (conExpr () "{}" []))

        succeedParse annExprParser
            "(x, y) => x"
            (lamExpr () [varPat () "x", varPat () "y"] (varExpr () "x"))

        succeedParse annExprParser
            "((x, y)) => x"
            (lamExpr () [tuplePat () [varPat () "x", varPat () "y"]] (varExpr () "x"))

        succeedParse annExprParser
            "(((x, y))) => x"
            (lamExpr () [tuplePat () [varPat () "x", varPat () "y"]] (varExpr () "x"))

        succeedParse annExprParser
            "[1, 2]"
            (listExpr () [litExpr () (TBig 1), litExpr () (TBig 2)])

        succeedParse annExprParser
            "[]"
            (conExpr () "[]" [])

        succeedParse annExprParser
            "[  ]"
            (conExpr () "[]" [])

        succeedParse annExprParser
            "let f() = () in f()"
            (letExpr () (BFun () "f" [litPat () TUnit]) (litExpr () TUnit) (appExpr () [varExpr () "f", litExpr () TUnit]))

        succeedParse annExprParser
            "length(xs) <= 3"
            (op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TBig 3)))

        succeedParse annExprParser
            "(length(xs) <= 3)"
            (op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TBig 3)))

        succeedParse annExprParser
            "((length(xs) <= 3))"
            (op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TBig 3)))

        succeedParse annExprParser
            "add(5, _)"
            (appExpr () [varExpr () "add", litExpr () (TBig 5), holeExpr ()])

        succeedParse annExprParser
            "add(5, _ : int)"
            (appExpr () [varExpr () "add", litExpr () (TBig 5), annExpr tInt (holeExpr ())])

        succeedParse annExprParser
            "r.a + 100"
            (op2Expr () (OAdd ()) (op2Expr () (ODot ()) (varExpr () "a") (varExpr () "r")) (litExpr () (TBig 100)))

        succeedParse annExprParser
            "5 + _"
            (op2Expr () (OAdd ()) (litExpr () (TBig 5)) (holeExpr ()))

        succeedParse annExprParser
            "_ + _"
            (op2Expr () (OAdd ()) (holeExpr ()) (holeExpr ()))

        failParse annExprParser "!5"

        succeedParse annExprParser
            "4.5"
            (litExpr () (TDouble 4.5))

        succeedParse annExprParser
            "4"
            (litExpr () (TBig 4))

        succeedParse annExprParser
            "4 : int"
            (annExpr tInt (litExpr () (TBig 4)))

        succeedParse annExprParser
            "(4 : int)"
            (annExpr tInt (litExpr () (TBig 4)))

        succeedParse annExprParser
            "(4)"
            (litExpr () (TBig 4))

        succeedParse annExprParser
            "((4))"
            (litExpr () (TBig 4))

        succeedParse annExprParser
            "((4) : int)"
            (annExpr tInt (litExpr () (TBig 4)))

        succeedParse annExprParser
            "(4) : int"
            (annExpr tInt (litExpr () (TBig 4)))

        succeedParse annExprParser
            "((4, 3) : int)"
            (annExpr tInt (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)]))

        succeedParse annExprParser
            "(((4, 3)))"
            (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])

        succeedParse annExprParser
            "((((4, 3))))"
            (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)])

        failParse annExprParser
            "((((4, 3)]]]"

        succeedParse annExprParser
            "(((4, 3) : int))"
            (annExpr tInt (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)]))

        succeedParse annExprParser
            "(4, 3) : int"
            (annExpr tInt (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)]))

        succeedParse annExprParser
            "if (4, 3) : int then (1, 3, 4) else (5, 6, 7)"
            (ifExpr ()
                (annExpr tInt (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)]))
                (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 3), litExpr () (TBig 4)])
                (tupleExpr () [litExpr () (TBig 5), litExpr () (TBig 6), litExpr () (TBig 7)]))

        succeedParse annExprParser
            "(if (4, 3) : int then (1, 3, 4) else (5, 6, 7)) : int"
            (annExpr tInt (ifExpr ()
                (annExpr tInt (tupleExpr () [litExpr () (TBig 4), litExpr () (TBig 3)]))
                (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 3), litExpr () (TBig 4)])
                (tupleExpr () [litExpr () (TBig 5), litExpr () (TBig 6), litExpr () (TBig 7)])))

        succeedParse annExprParser
            "fn(1 : int, 3, 4)"
            (appExpr () [varExpr () "fn", annExpr tInt (litExpr () (TBig 1)), litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "fn(1 : int, 3, 4) : int"
            (annExpr tInt (appExpr () [varExpr () "fn", annExpr tInt (litExpr () (TBig 1)), litExpr () (TBig 3), litExpr () (TBig 4)]))

        succeedParse annExprParser
            "fn(x : int, 3, 4)"
            (appExpr () [varExpr () "fn", annExpr tInt (varExpr () "x"), litExpr () (TBig 3), litExpr () (TBig 4)])

        succeedParse annExprParser
            "((fn(x))(y))"
            (appExpr () [appExpr () [varExpr () "fn", varExpr () "x"], varExpr () "y"])

        succeedParse exprParser
            "[1 : int, 2, 3]"
            (listExpr () [annExpr tInt (litExpr () (TBig 1)), litExpr () (TBig 2), litExpr () (TBig 3)])

        succeedParse exprParser
            "let x = (1, 2) : int in z"
            (letExpr () (BPat () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 2)])) (varExpr () "z"))

        succeedParse exprParser
            "let x = (1, 2) : int in z : int"
            (letExpr () (BPat () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 2)])) (annExpr tInt (varExpr () "z")))

        succeedParse annExprParser
            "(let x = (1, 2) : int in z : int) : int"
            (annExpr tInt (letExpr () (BPat () (varPat () "x")) (annExpr tInt (tupleExpr () [litExpr () (TBig 1), litExpr () (TBig 2)])) (annExpr tInt (varExpr () "z"))))

        succeedParse annExprParser
            "{ x = 5 : int }"
            (recordExpr () (rowExpr () "x" (annExpr tInt (litExpr () (TBig 5))) (conExpr () "{}" [])))

        succeedParse annExprParser
            "(x : int) => x + 1"
            (lamExpr () [annPat tInt (varPat () "x")] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))))

        succeedParse annExprParser
            "x : int => x + 1"
            (lamExpr () [annPat tInt (varPat () "x")] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1))))

        succeedParse annExprParser
            "Some(x) => x + 1 | None => 0"
            (funExpr () [ Clause () [conPat () "Some" [varPat () "x"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TBig 1)))] , Clause () [conPat () "None" []] [Choice [] (litExpr () (TBig 0))] ])

        succeedParse annExprParser
            "match (x, y) with | (1, x) when(x /= 0) => x, otherwise => 0 | _ => 100"
            (patExpr () (tupleExpr () [varExpr () "x", varExpr () "y"]) [ Clause () (tuplePat () [litPat () (TBig 1), varPat () "x"]) [Choice [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TBig 0))] (varExpr () "x"), Choice [] (litExpr () (TBig 0))] , Clause () (anyPat ()) [Choice [] (litExpr () (TBig 100))] ])

        succeedParse annExprParser
            "{ foo = x => \"Hello\" }.foo(false) }"
            (appExpr () [op2Expr () (ODot  ()) (varExpr () "foo") (recordExpr () (rowExpr () "foo" (lamExpr () [varPat () "x"] (litExpr () (TString "Hello"))) (conExpr () "{}" []))), litExpr () (TBool False)])

        succeedParse exprParser
            "(a + b) * c"
            (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) (varExpr () "c"))

        succeedParse annExprParser
            "(a + b) * c"
            (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) (varExpr () "c"))

        succeedParse annExprParser
            "((succ(5)+3)*0)"
            (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (litExpr () (TBig 0)))

        succeedParse annExprParser
            "((succ(5)+3)*zero)"
            (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (conExpr () "zero" []))

        succeedParse annExprParser
            "((succ(5)+3)*succ(zero))"
            (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (conExpr () "succ" [conExpr () "zero" []]))

        succeedParse annExprParser
            "((succ(5)+3)*succ(0))"
            (op2Expr () (OMul ()) (op2Expr () (OAdd ()) (conExpr () "succ" [litExpr () (TBig 5)]) (litExpr () (TBig 3))) (conExpr () "succ" [litExpr () (TBig 0)]))

        succeedParse annExprParser
            "(0-100):nat"
            (annExpr tNat (op2Expr () (OSub ()) (litExpr () (TBig 0)) (litExpr () (TBig 100))))

        succeedParse annExprParser
            "(zero-100):nat"
            (annExpr tNat (op2Expr () (OSub ()) (conExpr () "zero" []) (litExpr () (TBig 100))))

        succeedParse annExprParser
            "((5, y) => y | (_, _) => 9)(3, 8)"
            (appExpr () [funExpr () [ Clause () [litPat () (TBig 5), varPat () "y"] [Choice [] (varExpr () "y")] , Clause () [anyPat (), anyPat ()] [Choice [] (litExpr () (TBig 9))] ], litExpr () (TBig 3), litExpr () (TBig 8) ])

        succeedParse annExprParser
            "((5, y) => y | _ => 9)(3, 8)"
            (appExpr () [funExpr () [ Clause () [litPat () (TBig 5), varPat () "y"] [Choice [] (varExpr () "y")] , Clause () [anyPat ()] [Choice [] (litExpr () (TBig 9))] ], litExpr () (TBig 3), litExpr () (TBig 8) ])

    describe "• Topdecl" $ do

        succeedParse topdeclParser
            "f(x, y) = x"
            (Top () (BFun () "f" [varPat () "x", varPat () "y"]) (varExpr () "x"))

        succeedParse topdeclParser
            "foo = 5"
            (Top () (BPat () (varPat () "foo")) (litExpr () (TBig 5)))

        succeedParse topdeclParser
            "f | (5, y) => y | _ => x"
            (Top () (BPat () (varPat () "f")) (funExpr () [ Clause () [litPat () (TBig 5), varPat () "y"] [Choice [] (varExpr () "y")], Clause () [anyPat ()] [Choice [] (varExpr () "x")]]))
