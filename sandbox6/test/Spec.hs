{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad.Except (runExceptT)
import Data.Either (isLeft, isRight)
import Data.Fix (Fix(..))
import Data.Functor.Foldable (cata, para, embed)
import Data.Functor.Identity
import Data.Map.Strict (Map)
import Data.Text (Text, unpack)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Void
import Stuff
import Tau.Misc
import Tau.Prettyprinters
import Tau.Util (Name, runSupplyNats, prettyT, renderDoc)
import Test.Hspec hiding (describe, it)
import TextShow (showt)
import qualified Data.Map.Strict as Map
import qualified Data.Text  as Text
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

testDescription :: Type -> Type -> Text
testDescription t1 t2 = "The types " <> prettyT t1 <> " and " <> prettyT t2

succeedUnifyTypes :: Type -> Type -> SpecWith ()
succeedUnifyTypes t1 t2 = do
    let result = runUnify t1 t2
    describe (testDescription t1 t2) $ do
        it "✔ yields a substitution" $
            isRight result

        it "✔ and it unifies the two types" $ do
            let Right (typeSub, kindSub) = result
                r1 = apply kindSub (apply typeSub t1)
                r2 = apply kindSub (apply typeSub t2)
            canonicalRep r1 == canonicalRep r2

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

    describe "Row types" $ do

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

succeedMatchTypeVars :: Type -> [(Name, Kind)] -> SpecWith ()
succeedMatchTypeVars ty vars =
    describe ("The free type variables in " <> prettyT ty) $
        it ("✔ are [" <> Text.intercalate ", " (renderDoc . prettyTypePair <$> vars) <> "]")
            (typeVars ty == vars)
  where
    prettyTypePair (n, k) = pretty n <+> ":" <+> pretty k

testTypeVars :: SpecWith ()
testTypeVars = do

    succeedMatchTypeVars
        _a
        [("a", kTyp)]

    succeedMatchTypeVars
        (_a `tArr` _b)
        [("a", kTyp), ("b", kTyp)]

    succeedMatchTypeVars
        (tList _a `tArr` _b)
        [("a", kTyp), ("b", kTyp)]

    succeedMatchTypeVars
        tInt
        []

    succeedMatchTypeVars
        (tApp kTyp (tVar kFun "m") _a)
        [("m", kFun), ("a", kTyp)]

testKindOf :: SpecWith ()
testKindOf = do

    describe "The kind of Bool" $ do
        it "✔ is *"
            (kindOf tBool == kTyp)

    describe "The kind of (Int -> Int)" $ do
        it "✔ is *"
            (kindOf (tInt `tArr` tInt) == kTyp)

    describe "The kind of (List a)" $ do
        it "✔ is *"
            (kindOf (tList _a) == kTyp)

    describe "The kind of (List Int)" $ do
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

succeedInferExpr :: ProgExpr () Type -> Type -> SpecWith ()
succeedInferExpr expr ty = -- ps errs =
    describe ("The inferred type of the expression " <> prettyT expr) $ do
        it ("✔ is unifiable with " <> prettyT ty) $
            isRight res
  where
    (Ast e, (typeSub, kindSub, context)) =
        runInfer mempty testClassEnv testTypeEnv testKindEnv testConstructorEnv (inferAstType (Ast expr))

    res = runUnify (typeOf (applyBoth (typeSub, kindSub) e)) ty

testTypeInference :: SpecWith ()
testTypeInference = do

    succeedInferExpr
        (varExpr () "x")
        (tVar kTyp "a")

    succeedInferExpr
        (appExpr () [varExpr () "id", litExpr () (TInt 5)])
        (tVar kTyp "a")

    succeedInferExpr
        (appExpr () [varExpr () "id", annExpr tInt (litExpr () (TInteger 5))])
        tInt

    succeedInferExpr
        (appExpr () [varExpr () "id", litExpr () (TBool True)])
        tBool

    succeedInferExpr
        (varExpr () "id")
        (tVar kTyp "a" `tArr` tVar kTyp "a")

    succeedInferExpr
        (conExpr () "(::)" [litExpr () (TBool True), conExpr () "[]" []])
        (tList tBool)

    succeedInferExpr
        (listExpr () [litExpr () (TBool True)])
        (tList tBool)

    succeedInferExpr
        -- let x = () in x
        (letExpr () (BPat () (varPat () "x")) (litExpr () TUnit) (varExpr () "x"))
        tUnit

    succeedInferExpr
        -- let x = 5 in x
        (letExpr () (BPat () (varPat () "x")) (litExpr () (TInteger 5)) (varExpr () "x"))
        (tVar kTyp "a")
--        (HasPredicates [InClass "Num" "a"])

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))]))
        tInt

    succeedInferExpr
        (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (varExpr () "f"))
        (tVar kTyp "a" `tArr` tVar kTyp "a")

    succeedInferExpr
        (funExpr () [ Clause () [conPat () "(::)" [varPat () "x", conPat () "(::)" [varPat () "y", varPat () "ys"]]] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "[]" []] [Choice [] (litExpr () (TBool True))] , Clause () [conPat () "(::)" [varPat () "z", varPat () "zs"]] [Choice [] (litExpr () (TBool True))] ])
        (tList (tVar kTyp "a") `tArr` tBool)

    describe "• Records" $ do

        succeedInferExpr
            -- (let r = { a = 1 : Int, b = 2 : Int } in ({ a = a | z }) => a)({ a = 5 : Int })
            (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
            tInt

        -- let f(z) = { a = 1 : Int | z } in f({ b = 2 })
        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
            -- { a : Int, b : Int }
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

        -- ((z) => { a = 1 : Int | z })({ b = 2 : Int })
        succeedInferExpr
            (appExpr () [lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))), recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

        -- (z) => { a = 1 : Int | z }
        succeedInferExpr
            (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))))
            (tRecord (tVar kRow "r") `tArr` tRecord (tRow "a" tInt (tVar kRow "r")))

        -- ({ a = a | z }) => { z }
        succeedInferExpr
            (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z")))
            -- { a : a | r } -> { r }
            (tRecord (tRow "a" (tVar kTyp "a") (tVar kRow "r")) `tArr` tRecord (tVar kRow "r"))

        -- (({ a = a | z }) => { z })({ a = 1 })
        succeedInferExpr
            (appExpr ()
                [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z"))
                , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" [])) ])
            -- {}
            (tRecord (tCon kRow "{}"))

        -- (({ a = a | z }) => { z })({ a = 1, b = 2, d = 3 })
        succeedInferExpr
            (appExpr ()
                [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z"))
                , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1)))
                                (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2)))
                                (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3)))
                                (conExpr () "{}" [])))) ])
            (tRecord (tRow "b" tInt (tRow "d" tInt tRowNil)))

        succeedInferExpr
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (varExpr () "withDefault"))
            (tVar kTyp "a" `tArr` tApp kTyp (tCon kFun "Option") (tVar kTyp "a") `tArr` tVar kTyp "a")

        -- { a = 1 : Int, b = 2 : Int }.a
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
            tInt

        -- { a = (), b = 2 }.a
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))))
            tUnit

        -- let c = (_ => True) in { a = (), b = 2 }.c
        succeedInferExpr
            (letExpr () (BPat () (varPat () "c"))
                (lamExpr () [anyPat ()] (litExpr () (TBool True)))
                (op2Expr () (ODot ()) (varExpr () "c") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))))))
            tBool

        -- let c(_) = True in { a = (), b = 2 }.c
        succeedInferExpr
            (letExpr () (BFun () "c" [anyPat ()])
                (litExpr () (TBool True))
                (op2Expr () (ODot ()) (varExpr () "c") (recordExpr () (rowExpr () "a" (litExpr () TUnit) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))))))
            tBool

        -- { a = { b = { c = \"d\" } } }.a.b.c
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "c") (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (rowExpr () "b" (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" [])) (conExpr () "{}" [])) (conExpr () "{}" []))))))
            tString

        -- { a = { b = { c = \"d\" } } }.a.b
        succeedInferExpr
            (op2Expr () (ODot ()) (varExpr () "c") (op2Expr () (ODot ()) (varExpr () "b") (op2Expr () (ODot ()) (varExpr () "a") (recordExpr () (rowExpr () "a" (rowExpr () "b" (rowExpr () "c" (litExpr () (TString "d")) (conExpr () "{}" [])) (conExpr () "{}" [])) (conExpr () "{}" []))))))
            (tRecord (tRow "c" tString tRowNil))

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
        --         | [Nil']     => 0 : Int)
        --       in
        --         let xs = [2] : List Int
        --           in
        --             match xs with
        --               | [x :: _]
        --                   when(length(xs) <= 3) => x
        --               | [_]                     => 0
        --
        succeedInferExpr
            (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 2)])) (patExpr () (varExpr () "xs") [ Clause () (conPat () "(::)" [varPat () "x", anyPat ()]) [Choice [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () (anyPat ()) [Choice [] (litExpr () (TInteger 0))] ]))))
            tInt

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
            (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TInteger 1))) (conExpr () "{}" []))) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInteger 3))) (appExpr () [varExpr () "_#", varExpr () "r"]))))))
            (tRecord (tRow "a" tInt (tRow "b" tInt (tRow "d" tInt (tRow "z" tInt (tCon kRow "{}"))))))

        -- ((x, y) =>
        --   match (x, y) with
        --     | [(1 : Int, x)]
        --         when(x /= 0) => x
        --         otherwise    => 0 : Int
        --     | [_]            => 100 : Int)(1, 5)
        --
        succeedInferExpr
            (appExpr () [ lamExpr () [varPat () "x", varPat () "y"] (patExpr () (tupleExpr () [varExpr () "x", varExpr () "y"]) [ Clause () (tuplePat () [annPat tInt (litPat () (TInteger 1)), varPat () "x"])  [ Choice [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TInteger 0))] (varExpr () "x") , Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () (anyPat ()) [ Choice [] (annExpr tInt (litExpr () (TInteger 100))) ] ]) , litExpr () (TInteger 1) , litExpr () (TInteger 5) ])
            tInt

        succeedInferExpr
            (appExpr () [appExpr () [varExpr () "(+)", annExpr tInt (litExpr () (TInteger 5))], litExpr () (TInteger 5)])
            tInt

        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (op2Expr () (OSub ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "pred")) (appExpr () [varExpr () "f", holeExpr (), annExpr tInt (litExpr () (TInteger 1))]) (appExpr () [varExpr () "pred", litExpr () (TInteger 11)])))
            tInt

        succeedInferExpr
            (Fix (EOp2 () (ODot ()) (Fix (EVar () "c")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "b")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "a")) (Fix (ECon () "#" [Fix (ERow () "a" (Fix (ECon () "#" [Fix (ERow () "b" (Fix (ECon () "#" [Fix (ERow () "c" (Fix (ELit () (TString "d"))) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))]))))))))
            tString

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EAnn (Fix (TApp (Fix (KVar "k15")) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KCon "*")))) "List")) (Fix (TCon (Fix (KCon "*")) "Int")))) (Fix (EList () [Fix (ELit () (TInteger 1))])))) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PCon () "(::)" [Fix (PVar () "x"),Fix (PAny ())]), clauseChoices = [Choice [Fix (EOp2 () (OEq ()) (Fix (EVar () "x")) (Fix (ELit () (TInteger 1))))] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]}]))))
            tInt

        succeedInferExpr
            (letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BFun () "add5" [varPat () "z"]) (appExpr () [varExpr () "add", varExpr () "z", annExpr tInt (litExpr () (TInteger 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TInteger 3))])))
            tInt

        succeedInferExpr
            (letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "add5")) (appExpr () [varExpr () "add", holeExpr (), annExpr tInt (litExpr () (TInteger 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TInteger 3))])))
            tInt

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 1)))),Fix (ELit () (TInteger 2)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())]))))), clauseChoices = [Choice [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]}]))))
            tInt

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 5)))),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]}]))))
            tInt

        succeedInferExpr
            (Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 5)))),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [ Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")]), clauseChoices = [Choice [] (Fix (EVar () "x"))]} , Clause {clauseTag = (), clausePatterns = Fix (PAny ()), clauseChoices = [Choice [] (Fix (ELit () (TInteger 0)))]} ]))))
            tInt

        succeedInferExpr
            (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "map" [varPat () "f", varPat () "ys"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], varExpr () "a"])] , Clause () [conPat () "Nil'" []] [Choice [] (conExpr () "[]" [])] ] ]) (varExpr () "ys")) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , testList ]))))
            (tList tInt)

        succeedInferExpr
            (listExpr () [annExpr tInt (litExpr () (TInteger 2)), litExpr () (TInteger 3), litExpr () (TInteger 4), litExpr () (TInteger 5)])
            (tList tInt)

        succeedInferExpr
            (let testList = annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () (conPat () "(::)" [varPat () "x", varPat () "xs"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () (conPat () "[]" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] , varExpr () "testList" ])))
            tInt

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Choice [] (litExpr () (TInteger 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]]))
            tInt

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Choice [] (litExpr () (TInteger 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TInteger 100))]]))
            tInt

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Choice [] (litExpr () (TInteger 4)) ] , Clause () [conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] ]) (appExpr () [varExpr () "fn", annExpr (tApp kTyp (tCon kFun "Option") tInt) (conExpr () "None" [])]))
            tInt

        succeedInferExpr
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TInteger 5))]) (conExpr () "None" [])))
            tInt

        succeedInferExpr
            (letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Choice [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Choice [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TInteger 5))]) (conExpr () "Some" [annExpr tInt (litExpr () (TInteger 3))])))
            tInt

        succeedInferExpr
            (appExpr () [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) , annExpr tInt (litExpr () (TInteger 5)) , litExpr () (TInteger 3) ])
            tInt

        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Choice [] (litExpr () (TInteger 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TInteger 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "foo"), conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]]))
            tInt

        succeedInferExpr
            (letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Choice [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Choice [] (litExpr () (TInteger 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Choice [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (annExpr tInt (litExpr () (TInteger 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "baz"), conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]]))
            tInt

        succeedInferExpr
            (letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))]))
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

        succeedInferExpr
            (appExpr () [ lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) , recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])) ])
            (tRecord (tRow "a" tInt (tRow "b" tInt tRowNil)))

        succeedInferExpr
            (lamExpr () [recordPat () (varPat () "z")] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (varExpr () "z"))))
            (tArr (tRecord (tVar kRow "a")) (tRecord (tRow "a" tInt (tVar kRow "a"))))

        succeedInferExpr
            (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" [])) ])
            (tRecord tRowNil)

        succeedInferExpr
            (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" [])))) ])
            (tRecord (tRow "b" tInt (tRow "d" tInt tRowNil)))

        succeedInferExpr
            (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "c" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" []))))) (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z")), varExpr () "r" ]))
            (tRecord (tRow "b" tInt (tRow "c" tInt tRowNil)))

        --  fix map =
        --    f => fun | [[]] => [] | [x :: xs] => f(x) :: map(f, xs)
        --    in
        --      map(x => x + 1, [1, 2, 3] : List Int)
        succeedInferExpr
            (fixExpr () "map" (lamExpr () [varPat () "f"] (funExpr () [ Clause () [conPat () "[]" []] [ Choice [] (conExpr () "[]" []) ] , Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [ Choice [] (conExpr () "(::)" [ appExpr () [varExpr () "f", varExpr () "x"] , appExpr () [varExpr () "map", varExpr () "f", varExpr () "xs"] ]) ]])) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3)]) ]))
            (tList tInt)

        succeedInferExpr
            (fixExpr () "foldSucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "Succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldSucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (letExpr () (BFun () "toInt" [varPat () "n"]) (appExpr () [ varExpr () "foldSucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr tInt (litExpr () (TInteger 0)) , varExpr () "n" ]) (appExpr () [ varExpr () "foldSucc" , lamExpr () [varPat () "n", varPat () "x"] (op2Expr () (OMul ()) (appExpr () [varExpr () "toInt", varExpr () "n"]) (varExpr () "x")) , annExpr tInt (litExpr () (TInteger 1)) , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]]]] ])))
            tInt

        succeedInferExpr
            (let testTree = conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 5)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 3)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 1)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 4)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 7)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Leaf" [] ] ] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 6)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] ] ] in letExpr () (BPat () (varPat () "testTree")) testTree (fixExpr () "loopTree" (lamExpr () [varPat () "g", varPat () "t"] (patExpr () (varExpr () "t") [ Clause () (conPat () "Node" [varPat () "n", varPat () "t1", varPat () "t2"]) [Choice [] (appExpr () [varExpr () "g", conExpr () "Node'" [varExpr () "n", varExpr () "t1", varExpr () "t2", appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t1"], appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t2"]]])] , Clause () (conPat () "Leaf" []) [Choice [] (appExpr () [varExpr () "g", conExpr () "Leaf'" []])] ])) (appExpr () [ varExpr () "loopTree" , funExpr () [ Clause () [conPat () "Node'" [varPat () "n", varPat () "t1", varPat () "t2", varPat () "a", varPat () "b"]] [Choice [] (op2Expr () (OAdd ()) (varExpr () "n") (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))] , Clause () [conPat () "Leaf'" []] [Choice [] (annExpr tInt (litExpr () (TInteger 0)))] ] , varExpr () "testTree" ])))
            tInt

        succeedInferExpr
            (fixExpr () "foldSucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "Succ" [varPat () "n"]] [Choice [] (appExpr () [ varExpr () "foldSucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Choice [] (varExpr () "a")] ])) (appExpr () [ varExpr () "foldSucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr tInt (litExpr () (TInteger 0)) , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]] ]))
            tInt

        succeedInferExpr
            (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (recordExpr () (varExpr () "z"))) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
            (tRecord tRowNil)

        succeedInferExpr
            (appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ])
            tInt

        -- let r = { a = 1 : Int, b = 2 : Int } in r.b
        succeedInferExpr
            (letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (op2Expr () (ODot ()) (varExpr () "b") (varExpr () "r")))
            tInt

        -- let f(x) = x + 1 in f(123 : Int)
        succeedInferExpr
            (letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))]))
            tInt

        -- ( fun
        --     | (True, Some(True))  => 1 : Int
        --     | (True, Some(False)) => 2
        --     | (_, _)              => 3 )(True, Some(False))
        --
        succeedInferExpr
            (appExpr () [ funExpr () [ Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]] [ Choice [] (annExpr tInt (litExpr () (TInt 1))) ] , Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]] [ Choice [] (litExpr () (TInt 2)) ] , Clause () [anyPat (), anyPat ()] [ Choice [] (litExpr () (TInt 3)) ] ] , litExpr () (TBool True) , conExpr () "Some" [litExpr () (TBool False)] ])
            tInt

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

    describe "• Type" $ do

        suceedPrintType
            (_a `tArr` _b)
            "a -> b"

        suceedPrintType
            tInt
            "Int"

        suceedPrintType
            (_a `tArr` _b `tArr` _c)
            "a -> b -> c"

        suceedPrintType
            ((_a `tArr` _b) `tArr` _c)
            "(a -> b) -> c"

        suceedPrintType
            (tList tInt `tArr` _b `tArr` _c)
            "List Int -> b -> c"

        suceedPrintType
            (tList (tList tInt))
            "List (List Int)"

        suceedPrintType
            (tList (tInt `tArr` _a))
            "List (Int -> a)"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") tInt) tInt)
            "C Int Int"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") tInt) tInt `tArr` _a)
            "C Int Int -> a"

        suceedPrintType
            (tApp kTyp (tApp kFun (tCon kFun2 "C") (_a `tArr` _a)) tInt `tArr` _a)
            "C (a -> a) Int -> a"

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
            (tApp kTyp (tApp kTyp (tCon (kArr kTyp (kArr kTyp kTyp)) "(,)") (tCon kTyp "String")) (tCon kTyp "Bool"))
            "(String, Bool)"

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

--    --    suceedPrintPattern
--    --        (recordPat () (rExt "id" (varPat () "id") (rExt "name" (varPat () "name") rNil)))
--    --        "{ id = id, name = name }"
--    --
--    --    suceedPrintPattern
--    --        (recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") rNil)))
--    --        "{ id = id, name = name }"
--    --
--    --    suceedPrintPattern
--    --        (recordPat () (rExt "name" (anyPat ()) (rExt "id" (varPat () "id") rNil)))
--    --        "{ id = id, name = _ }"
--    --
--    --    suceedPrintPattern
--    --        (recordPat () (rExt "name" (varPat () "name") (rExt "id" (varPat () "id") (rVar (varPat () "r")))))
--    --        "{ id = id, name = name | r }"

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

    describe "• Predicates" $ do

        suceedPrint
            (InClass "Show" _a)
            "Show a"

        suceedPrint
            (InClass "Eq" tInt :: Predicate)
            "Eq Int"

    describe "• Expr" $ do

        suceedPrintExpr
            (appExpr () [varExpr () "add", litExpr () (TInteger 3), holeExpr ()])
            "add(3, _)"

        suceedPrintExpr
            (tupleExpr () [varExpr () "x", litExpr () (TInt 5)])
            "(x, 5)"

        describe "• Datatype expressions" $ do

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
