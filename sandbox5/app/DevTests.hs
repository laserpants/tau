{-# LANGUAGE OverloadedStrings #-}
module DevTests where

import Control.Monad.Reader
import Data.Maybe
import Data.Text (Text)
import Tau.Compiler.Bundle
import Tau.Core
import Tau.Eval
import Tau.Lang
import Tau.Parser
import Tau.Prog
import Tau.Serialize
import Tau.Type
import Tau.Util
import qualified Tau.Env as Env

expr1 :: ProgExpr ()
expr1 = letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "z" (annExpr tInt (litExpr () (TInteger 1))) (conExpr () "{}" []))) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInteger 3))) (appExpr () [varExpr () "_#", varExpr () "r"]))))) 

expr1_result :: ProgExpr ()
expr1_result = recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInteger 3))) (rowExpr () "z" (annExpr tInt (litExpr () (TInteger 1))) (conExpr () "{}" [])))))

-------------------------------------------------------------------------------

-- (Value (TInt 2))
expr2 :: ProgExpr ()
expr2 = (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () [conPat () "[]" []] [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "length" [varPat () "xs"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [anyPat (), anyPat (), varPat () "a"]] [Guard [] (op2Expr () (OAdd ()) (litExpr () (TInteger 1)) (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))] ] ]) (varExpr () "xs")) (letExpr () (BPat () (varPat () "xs")) (annExpr (tList tInt) (listExpr () [litExpr () (TInteger 2)])) (patExpr () (varExpr () "xs") [ Clause () [conPat () "(::)" [varPat () "x", anyPat ()]] [Guard [op2Expr () (OLte ()) (appExpr () [varExpr () "length", varExpr () "xs"]) (litExpr () (TInteger 3))] (varExpr () "x")] , Clause () [anyPat ()] [Guard [] (litExpr () (TInteger 0))] ])))) 

-------------------------------------------------------------------------------

-- (Value (TInt 5))
expr3 :: ProgExpr ()
expr3 = appExpr () [ lamExpr () [varPat () "x", varPat () "y"] (patExpr () (tupleExpr () [varExpr () "x", varExpr () "y"]) [ Clause () [tuplePat () [annPat tInt (litPat () (TInteger 1)), varPat () "x"]]  [ Guard [op2Expr () (ONeq ()) (varExpr () "x") (litExpr () (TInteger 0))] (varExpr () "x") , Guard [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () [anyPat ()] [ Guard [] (annExpr tInt (litExpr () (TInteger 100))) ] ]) , litExpr () (TInteger 1) , litExpr () (TInteger 5) ]

-------------------------------------------------------------------------------

-- (Value (TInt 10))
expr4 :: ProgExpr ()
expr4 = appExpr () [appExpr () [varExpr () "(+)", annExpr tInt (litExpr () (TInteger 5))], litExpr () (TInteger 5)]

-------------------------------------------------------------------------------

-- (Value (TInt 10))
expr5 :: ProgExpr ()
expr5 = letExpr () (BFun () "f" [varPat () "x", varPat () "y"]) (op2Expr () (OSub ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "pred")) (appExpr () [varExpr () "f", holeExpr (), annExpr tInt (litExpr () (TInteger 1))]) (appExpr () [varExpr () "pred", litExpr () (TInteger 11)]))

-------------------------------------------------------------------------------

-- Value (TString "d")
expr6 :: ProgExpr ()
expr6 = Fix (EOp2 () (ODot ()) (Fix (EVar () "c")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "b")) (Fix (EOp2 () (ODot ()) (Fix (EVar () "a")) (Fix (ECon () "#" [Fix (ERow () "a" (Fix (ECon () "#" [Fix (ERow () "b" (Fix (ECon () "#" [Fix (ERow () "c" (Fix (ELit () (TString "d"))) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])) (Fix (ECon () "{}" [])))])))))))

-------------------------------------------------------------------------------

-- Value (TInt 1)
expr7 :: ProgExpr ()
expr7 = Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EAnn (Fix (TApp (Fix (KVar "k15")) (Fix (TCon (Fix (KArr (Fix (KCon "*")) (Fix (KCon "*")))) "List")) (Fix (TCon (Fix (KCon "*")) "Int")))) (Fix (EList () [Fix (ELit () (TInteger 1))])))) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = [Fix (PCon () "(::)" [Fix (PVar () "x"),Fix (PAny ())])], clauseGuard = [Guard [Fix (EOp2 () (OEq ()) (Fix (EVar () "x")) (Fix (ELit () (TInteger 1))))] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PAny ())], clauseGuard = [Guard [] (Fix (ELit () (TInteger 0)))]}])))

-------------------------------------------------------------------------------

-- Value (TInt 8)
expr8 :: ProgExpr ()
expr8 = letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BFun () "add5" [varPat () "z"]) (appExpr () [varExpr () "add", varExpr () "z", annExpr tInt (litExpr () (TInteger 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TInteger 3))]))

-------------------------------------------------------------------------------

-- Value (TInt 8)
expr9 :: ProgExpr ()
expr9 = letExpr () (BFun () "add" [varPat () "x", varPat () "y"]) (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "y")) (letExpr () (BPat () (varPat () "add5")) (appExpr () [varExpr () "add", holeExpr (), annExpr tInt (litExpr () (TInteger 5))]) (appExpr () [varExpr () "add5", annExpr tInt (litExpr () (TInteger 3))]))

-------------------------------------------------------------------------------

-- Value (TInt 1)
expr10 :: ProgExpr ()
expr10 = Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 1)))),Fix (ELit () (TInteger 2)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = [Fix (POr () (Fix (PList () [Fix (PVar () "x")])) (Fix (POr () (Fix (PList () [Fix (PVar () "x"),Fix (PAny ())])) (Fix (PList () [Fix (PVar () "x"),Fix (PAny ()),Fix (PAny ())])))))], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PAny ())], clauseGuard = [Guard [] (Fix (ELit () (TInteger 0)))]}])))

-------------------------------------------------------------------------------

-- Value (TInt 0)
expr11 :: ProgExpr ()
expr11 = Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 5)))),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = [Fix (PList () [Fix (PVar () "x")])], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")])], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")])], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PAny ())], clauseGuard = [Guard [] (Fix (ELit () (TInteger 0)))]}])))

-------------------------------------------------------------------------------

-- Value (TInt 5)
expr12 :: ProgExpr ()
expr12 = Fix (ELet () (BPat () (Fix (PVar () "xs"))) (Fix (EList () [Fix (EAnn (Fix (TCon (Fix (KCon "*")) "Int")) (Fix (ELit () (TInteger 5)))),Fix (ELit () (TInteger 3)),Fix (ELit () (TInteger 3))])) (Fix (EPat () (Fix (EVar () "xs")) [Clause {clauseTag = (), clausePatterns = [Fix (PList () [Fix (PVar () "x")])], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y")])], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PList () [Fix (PVar () "x"),Fix (PVar () "y"),Fix (PVar () "z")])], clauseGuard = [Guard [] (Fix (EVar () "x"))]},Clause {clauseTag = (), clausePatterns = [Fix (PAny ())], clauseGuard = [Guard [] (Fix (ELit () (TInteger 0)))]}])))

-------------------------------------------------------------------------------

expr13 :: ProgExpr ()
expr13 = let testList = annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () [conPat () "[]" []] [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (letExpr () (BFun () "map" [varPat () "f", varPat () "ys"]) (op2Expr () (ODot ()) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Guard [] (conExpr () "(::)" [appExpr () [varExpr () "f", varExpr () "x"], varExpr () "a"])] , Clause () [conPat () "Nil'" []] [Guard [] (conExpr () "[]" [])] ] ]) (varExpr () "ys")) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , testList ])))

expr13_result :: ProgExpr ()
expr13_result = listExpr () [annExpr tInt (litExpr () (TInteger 2)), litExpr () (TInteger 3), litExpr () (TInteger 4), litExpr () (TInteger 5)]

-------------------------------------------------------------------------------

-- Value (TInt 10)
expr14 :: ProgExpr ()
expr14 = let testList = annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3), litExpr () (TInteger 4)]) in letExpr () (BPat () (varPat () "testList")) testList (fixExpr () "loopList" (lamExpr () [varPat () "g", varPat () "ys"] (patExpr () (varExpr () "ys") [ Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [Guard [] (appExpr () [varExpr () "g", conExpr () "Cons'" [varExpr () "x", varExpr () "xs", appExpr () [varExpr () "loopList", varExpr () "g", varExpr () "xs"]]])] , Clause () [conPat () "[]" []] [Guard [] (appExpr () [varExpr () "g", conExpr () "Nil'" []])] ])) (appExpr () [ varExpr () "loopList" , funExpr () [ Clause () [conPat () "Cons'" [varPat () "x", varPat () "xs", varPat () "a"]] [Guard [] (op2Expr () (OAdd ()) (varExpr () "x") (varExpr () "a"))] , Clause () [conPat () "Nil'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))] ] , varExpr () "testList" ]))

-------------------------------------------------------------------------------

-- Value (TInt 2)
expr15 :: ProgExpr ()
expr15 = letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Guard [] (litExpr () (TInteger 4)) ] , Clause () [conPat () "None" []] [ Guard [] (annExpr tInt (litExpr () (TInteger 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]])

-------------------------------------------------------------------------------

-- Value (TInt 4)
expr16 :: ProgExpr ()
expr16 = letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Guard [] (litExpr () (TInteger 4)) ] , Clause () [conPat () "None" []] [ Guard [] (annExpr tInt (litExpr () (TInteger 0))) ] ]) (appExpr () [varExpr () "fn", conExpr () "Some" [annExpr tInt (litExpr () (TInteger 100))]])

-------------------------------------------------------------------------------

-- Value (TInt 0)
expr17 :: ProgExpr ()
expr17 = letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Guard [] (litExpr () (TInteger 4)) ] , Clause () [conPat () "None" []] [ Guard [] (annExpr tInt (litExpr () (TInteger 0))) ] ]) (appExpr () [varExpr () "fn", annExpr (tApp kTyp (tCon kFun "Option") tInt) (conExpr () "None" [])])

-------------------------------------------------------------------------------

-- Value (TInt 5)
expr18 :: ProgExpr ()
expr18 = letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Guard [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TInteger 5))]) (conExpr () "None" []))

-------------------------------------------------------------------------------

-- Value (TInt 3)
expr19 :: ProgExpr ()
expr19 = letExpr () (BFun () "withDefault" [varPat () "val"]) (funExpr () [ Clause () [conPat () "Some" [varPat () "y"]] [ Guard [] (varExpr () "y") ] , Clause () [conPat () "None" []] [ Guard [] (varExpr () "val") ] ]) (op2Expr () (ODot ()) (appExpr () [varExpr () "withDefault", annExpr tInt (litExpr () (TInteger 5))]) (conExpr () "Some" [annExpr tInt (litExpr () (TInteger 3))]))

-------------------------------------------------------------------------------

-- Value (TInt 8)
expr20 :: ProgExpr ()
expr20 = appExpr () [ lamExpr () [varPat () "a", varPat () "b"] (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")) , annExpr tInt (litExpr () (TInteger 5)) , litExpr () (TInteger 3) ]

-------------------------------------------------------------------------------

expr21 :: ProgExpr ()
expr21 = letExpr () (BFun () "f" [varPat () "z"]) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])

expr21_result :: ProgExpr ()
expr21_result = recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (conExpr () "{}" [])))

-------------------------------------------------------------------------------

-- Value (TInt 2)
expr22 :: ProgExpr ()
expr22 = letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Guard [] (litExpr () (TInteger 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Guard [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () [anyPat (), anyPat ()] [ Guard [] (annExpr tInt (litExpr () (TInteger 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "foo"), conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]])

-------------------------------------------------------------------------------

-- Value (TInt 999)
expr23 :: ProgExpr ()
expr23 = letExpr () (BPat () (varPat () "fn")) (funExpr () [ Clause () [litPat () (TString "foo"), conPat () "Some" [varPat () "y"]] [ Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 1))] (litExpr () (TInteger 1)) , Guard [op2Expr () (OEq ()) (varExpr () "y") (litExpr () (TInteger 2))] (litExpr () (TInteger 2)) , Guard [] (litExpr () (TInteger 4)) ] , Clause () [anyPat (), conPat () "None" []] [ Guard [] (annExpr tInt (litExpr () (TInteger 0))) ] , Clause () [anyPat (), anyPat ()] [ Guard [] (annExpr tInt (litExpr () (TInteger 999))) ] ]) (appExpr () [varExpr () "fn", litExpr () (TString "baz"), conExpr () "Some" [annExpr tInt (litExpr () (TInteger 2))]])

-------------------------------------------------------------------------------

expr24 :: ProgExpr ()
expr24 = letExpr () (BPat () (varPat () "f")) (lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))) (appExpr () [varExpr () "f", recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" []))])

expr24_result :: ProgExpr ()
expr24_result = recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (conExpr () "{}" [])))

-------------------------------------------------------------------------------

expr25 :: ProgExpr ()
expr25 = appExpr () [ lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"]))) , recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])) ]

-------------------------------------------------------------------------------

expr26 :: ProgExpr ()
expr26 = lamExpr () [varPat () "z"] (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInteger 1))) (appExpr () [varExpr () "_#", varExpr () "z"])))

-------------------------------------------------------------------------------

expr27 :: ProgExpr ()
expr27 = lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")

-------------------------------------------------------------------------------

-- Data "#" [Data "{}" []]
expr28 :: ProgExpr ()
expr28 = appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z") , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (conExpr () "{}" [])) ]

-------------------------------------------------------------------------------

expr29 :: ProgExpr ()
expr29 = appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z") , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" [])))) ]

expr29_result :: ProgExpr ()
expr29_result = recordExpr () (rowExpr () "b" (annExpr tInt (litExpr () (TInteger 2))) (rowExpr () "d" (annExpr tInt (litExpr () (TInteger 3))) (conExpr () "{}" [])))

-------------------------------------------------------------------------------

-- Data "#" [Data "{b}" [Value (TInt 2),Data "{c}" [Value (TInt 3),Data "{}" []]]] 
expr30 :: ProgExpr ()
expr30 = letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (rowExpr () "c" (annExpr tInt (litExpr () (TInt 3))) (conExpr () "{}" []))))) (appExpr () [ lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z") , varExpr () "r" ])

-------------------------------------------------------------------------------

expr31 :: ProgExpr ()
expr31 = (fixExpr () "map" (lamExpr () [varPat () "f"] (funExpr () [ Clause () [conPat () "[]" []] [ Guard [] (conExpr () "[]" []) ] , Clause () [conPat () "(::)" [varPat () "x", varPat () "xs"]] [ Guard [] (conExpr () "(::)" [ appExpr () [varExpr () "f", varExpr () "x"] , appExpr () [varExpr () "map", varExpr () "f", varExpr () "xs"] ]) ]])) (appExpr () [ varExpr () "map" , lamExpr () [varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr (tList tInt) (listExpr () [litExpr () (TInteger 1), litExpr () (TInteger 2), litExpr () (TInteger 3)]) ]))

expr31_result :: ProgExpr ()
expr31_result = listExpr () [annExpr tInt (litExpr () (TInteger 2)), litExpr () (TInteger 3), litExpr () (TInteger 4)]

-------------------------------------------------------------------------------

-- Value (TInt 120)
expr32 :: ProgExpr ()
expr32 = (fixExpr () "foldSucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "Succ" [varPat () "n"]] [Guard [] (appExpr () [ varExpr () "foldSucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Guard [] (varExpr () "a")] ])) (letExpr () (BFun () "toInt" [varPat () "n"]) (appExpr () [ varExpr () "foldSucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr tInt (litExpr () (TInteger 0)) , varExpr () "n" ]) (appExpr () [ varExpr () "foldSucc" , lamExpr () [varPat () "n", varPat () "x"] (op2Expr () (OMul ()) (appExpr () [varExpr () "toInt", varExpr () "n"]) (varExpr () "x")) , annExpr tInt (litExpr () (TInteger 1)) , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]]]] ])))

-------------------------------------------------------------------------------

-- Value (TInt 46)
expr33 :: ProgExpr ()
expr33 = let testTree = conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 5)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 3)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 1)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 4)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 7)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Leaf" [] ] ] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 6)) , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 2)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] , conExpr () "Node" [ annExpr tInt (litExpr () (TInteger 8)) , conExpr () "Leaf" [] , conExpr () "Leaf" [] ] ] ] in letExpr () (BPat () (varPat () "testTree")) testTree (fixExpr () "loopTree" (lamExpr () [varPat () "g", varPat () "t"] (patExpr () (varExpr () "t") [ Clause () [conPat () "Node" [varPat () "n", varPat () "t1", varPat () "t2"]] [Guard [] (appExpr () [varExpr () "g", conExpr () "Node'" [varExpr () "n", varExpr () "t1", varExpr () "t2", appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t1"], appExpr () [varExpr () "loopTree", varExpr () "g", varExpr () "t2"]]])] , Clause () [conPat () "Leaf" []] [Guard [] (appExpr () [varExpr () "g", conExpr () "Leaf'" []])] ])) (appExpr () [ varExpr () "loopTree" , funExpr () [ Clause () [conPat () "Node'" [varPat () "n", varPat () "t1", varPat () "t2", varPat () "a", varPat () "b"]] [Guard [] (op2Expr () (OAdd ()) (varExpr () "n") (op2Expr () (OAdd ()) (varExpr () "a") (varExpr () "b")))] , Clause () [conPat () "Leaf'" []] [Guard [] (annExpr tInt (litExpr () (TInteger 0)))] ] , varExpr () "testTree" ]))

-------------------------------------------------------------------------------

-- Value (TInt 3)
expr34 :: ProgExpr ()
expr34 = (fixExpr () "foldSucc" (lamExpr () [varPat () "g", varPat () "a"] (funExpr () [ Clause () [conPat () "Succ" [varPat () "n"]] [Guard [] (appExpr () [ varExpr () "foldSucc" , varExpr () "g" , appExpr () [varExpr () "g", conExpr () "Succ" [varExpr () "n"], varExpr () "a"] , varExpr () "n" ])] , Clause () [anyPat ()] [Guard [] (varExpr () "a")] ])) (appExpr () [ varExpr () "foldSucc" , lamExpr () [anyPat (), varPat () "x"] (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInteger 1))) , annExpr tInt (litExpr () (TInteger 0)) , conExpr () "Succ" [conExpr () "Succ" [conExpr () "Succ" [conExpr () "Zero" []]]] ]))

-------------------------------------------------------------------------------

-- Data "#" [Data "{}" []]
expr35 :: ProgExpr ()
expr35 = appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "z")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ]

-------------------------------------------------------------------------------

-- Value (TInt 5)
expr36 :: ProgExpr ()
expr36 = appExpr () [ letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (lamExpr () [recordPat () (rowPat () "a" (varPat () "a") (varPat () "z"))] (varExpr () "a")) , recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 5))) (conExpr () "{}" [])) ]

-------------------------------------------------------------------------------

-- Value (TInt 2)
expr37 :: ProgExpr ()
expr37 = letExpr () (BPat () (varPat () "r")) (recordExpr () (rowExpr () "a" (annExpr tInt (litExpr () (TInt 1))) (rowExpr () "b" (annExpr tInt (litExpr () (TInt 2))) (conExpr () "{}" [])))) (op2Expr () (ODot ()) (varExpr () "b") (varExpr () "r"))

-------------------------------------------------------------------------------

-- Value (TInt 124)
expr38 :: ProgExpr ()
expr38 = letExpr () (BFun () "f" [varPat () "x"]) (op2Expr () (OAdd ()) (varExpr () "x") (litExpr () (TInt 1))) (appExpr () [varExpr () "f", annExpr tInt (litExpr () (TInt 123))])

-------------------------------------------------------------------------------

-- Value (TInt 2)
expr39 :: ProgExpr ()
expr39 = appExpr () [ (funExpr () [ Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool True)]] [ Guard [] (annExpr tInt (litExpr () (TInt 1))) ] , Clause () [litPat () (TBool True), conPat () "Some" [litPat () (TBool False)]] [ Guard [] (litExpr () (TInt 2)) ] , Clause () [anyPat (), anyPat ()] [ Guard [] (litExpr () (TInt 3)) ] ]) , litExpr () (TBool True) , conExpr () "Some" [litExpr () (TBool False)] ]



-------------------------------------------------------------------------------


arbitraryTests :: IO ()
arbitraryTests = do
    a <- runExprTest expr1
    b <- runExprTest expr1_result

    let res1 = (a == b)

    -- (Value (TInt 2))
    a <- runExprTest expr2
    let res2 = (a == Just (Value (TInt 2)))



    traceShowM res1
    traceShowM res2

    pure ()

    



runExprTest expr = do -- foo1 expr
    traceShowM (pretty expr)
    bundle <- runReaderT (compileBundle expr) (testClassEnv, testTypeEnv, testKindEnv, testConstructorEnv) 

    --    let value  = join (evalExpr <$> (coreExpr bundle) <*> Just testEvalEnv)
    let value2 = join (evalExpr <$> (stageX6Expr bundle) <*> Just testEvalEnv)

    --    traceShowM value
    traceShowM value2

    --    liftIO $ LBS.writeFile "/home/laserpants/code/tau-tooling/src/tmp/bundle.json" (encodePretty' defConfig{ confIndent = Spaces 2 } 
    --                (toRep (bundle{ value = value, value2 = value2 })))

    --    traceShowM value

    pure value2


testKindEnv :: KindEnv
testKindEnv = Env.fromList
    [ ( "Num" , kArr kTyp kClass )
    ]

testTypeEnv :: TypeEnv
testTypeEnv = Env.fromList
    [ ( "None"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Some"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Option") (tGen 0)) )
    , ( "Zero"         , Forall []     [] (tCon kTyp "Nat") )
    , ( "Succ"         , Forall []     [] (tCon kTyp "Nat" `tArr` tCon kTyp "Nat") )
    , ( "Leaf"         , Forall [kTyp] [] (tApp kTyp (tCon kFun "Tree") (tGen 0)) )
    , ( "Node"         , Forall [kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0)) )

    , ( "Leaf'"        , Forall [kTyp, kTyp] [] (tApp kTyp (tApp kFun (tCon kFun2 "Tree'") (tGen 0)) (tGen 1)) )
    , ( "Node'"        , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tApp kTyp (tCon kFun "Tree") (tGen 0) `tArr` tGen 1 `tArr` tGen 1 `tArr` tApp kTyp (tApp kFun (tCon kFun2 "Tree'") (tGen 0)) (tGen 1)) )

    , ( "Nil'"         , Forall [kTyp, kTyp] [] (tApp kTyp (tApp kFun (tCon kFun2 "List'") (tGen 0)) (tGen 1)) )
    , ( "Cons'"        , Forall [kTyp, kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tGen 1 `tArr` tApp kTyp (tApp kFun (tCon kFun2 "List'") (tGen 0)) (tGen 1)) )

    , ( "Foo"          , Forall [] [] (tInt `tArr` tInt `tArr` tCon kTyp "Foo") )
    , ( "id"           , Forall [kTyp] [] (tGen 0 `tArr` tGen 0) )
    , ( "(::)"         , Forall [kTyp] [] (tGen 0 `tArr` tList (tGen 0) `tArr` tList (tGen 0)) )

    -- TEMP
    , ( "(==)"         , Forall [kTyp] [InClass "Eq" 0] (tGen 0 `tArr` tGen 0 `tArr` tBool) )

    , ( "testFun1"     , Forall [kTyp] [InClass "Num" 0, InClass "Eq" 0] (tGen 0 `tArr` tBool) )
    , ( "length"       , Forall [kTyp] [] (tList (tGen 0) `tArr` tInt) )

    , ( "[]"           , Forall [kTyp] [] (tList (tGen 0)) )
    , ( "(+)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(-)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "(*)"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0) )
    , ( "#"            , Forall [kRow] [] (tGen 0 `tArr` tApp kTyp tRecordCon (tGen 0)) )
    , ( "{}"           , Forall [] [] tRowNil )
    , ( "_#"           , Forall [kRow] [] (tApp kTyp (tCon (kArr kRow kTyp) "#") (tGen 0) `tArr` tGen 0) )
    , ( "fromInteger"  , Forall [kTyp] [InClass "Num" 0] (tInteger `tArr` tGen 0) )
    , ( "fn1"          , Forall [kTyp] [InClass "Num" 0] (tGen 0 `tArr` tGen 0 `tArr` tGen 0))

    , ( "show"         , Forall [kTyp] [InClass "Show" 0] (tGen 0 `tArr` tString) )
    , ( "read"         , Forall [kTyp] [InClass "Read" 0] (tString `tArr` tGen 0) )

    , ( "isLongerThan" , Forall [] [] (tInt `tArr` tString `tArr` tBool) )

    ]

testClassEnv :: ClassEnv
testClassEnv = Env.fromList
    [ ( "Read"
        -- Interface
      , ( ClassInfo (InClass "Read" "a") []  
            [ ( "read", tString `tArr` tVar kTyp "a"  )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) [] 
              [ ( "read", Ast (varExpr (TypeInfo () (tString `tArr` tString) []) "@Int.read") )
              ]
          ]
        )
      )
    , ( "Show"
        -- Interface
      , ( ClassInfo (InClass "Show" "a") []  
            [ ( "show", tVar kTyp "a" `tArr` tString )
            ]
        -- Instances
        , [ ClassInfo (InClass "Show" tInt) [] 
              [ ( "show", Ast (varExpr (TypeInfo () (tInt `tArr` tString) []) "@Int.show") )
              ]
          , ClassInfo (InClass "Show" (tPair (tVar kTyp "a") (tVar kTyp "b"))) [] 
              [ ( "show", Ast (varExpr (TypeInfo () (tPair (tVar kTyp "a") (tVar kTyp "b") `tArr` tString) []) "TODO") )
              ]
          ]
        )
      )
    , ( "Ord"
        -- Interface
      , ( ClassInfo (InClass "Ord" "a") [] 
            [ ( "(>)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(<)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(>=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            , ( "(<=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool ) 
            ]
        -- Instances
        , [ ClassInfo (InClass "Ord" tInt) [] 
              [ ( "(>)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>)") ) 
              , ( "(<)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<)") ) 
              , ( "(>=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(>=)") ) 
              , ( "(<=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(<=)") ) 
              ]
          ]
        )
      )
    , ( "Eq"
        -- Interface
      , ( ClassInfo (InClass "Eq" "a") [] -- [InClass "Ord" "a"] 
            [ ( "(==)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            , ( "(/=)", tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tBool )
            ]
        -- Instances
        , [ ClassInfo (InClass "Eq" tInt) [] 
            [ ( "(==)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Int.(/=)" ) )
            ]
          , ClassInfo (InClass "Eq" tInteger) [] 
            [ ( "(==)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Integer.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tBool) []) "@Integer.(/=)" ) )
            ]
          , ClassInfo (InClass "Eq" tBool) [] 
            [ ( "(==)", Ast (varExpr (TypeInfo () (tBool `tArr` tBool `tArr` tBool) []) "@Bool.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tBool `tArr` tBool `tArr` tBool) []) "@Bool.(/=)" ) )
            ]
          , ClassInfo (InClass "Eq" tString) [] 
            [ ( "(==)", Ast (varExpr (TypeInfo () (tString `tArr` tString `tArr` tString) []) "@String.(==)" ) )
            , ( "(/=)", Ast (varExpr (TypeInfo () (tString `tArr` tString `tArr` tString) []) "@String.(/=)" ) )
            ]
          ]
        )
      )
    , ( "Foo"
        -- Interface
      , ( ClassInfo (InClass "Foo" "a") [] 
            -- [ ( "foo", tInt ) 
            [ ( "foo", tBool ) 
            ]
        -- Instances
        , [ ClassInfo (InClass "Foo" tInt) [] 
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 5))) ) 
            [ ( "foo", (Ast (litExpr (TypeInfo () tBool []) (TBool True))) ) ]
          , ClassInfo (InClass "Foo" tInteger) [] 
            -- [ ( "foo", (Ast (litExpr (TypeInfo () tInt []) (TInt 7))) ) 
            [ ( "foo", (Ast (litExpr (TypeInfo () tBool []) (TBool False))) ) ]
          ]
        )
      )
    , ( "Num"
        -- Interface
      , ( ClassInfo (InClass "Num" "a") [InClass "Eq" "a", InClass "Foo" "a"]
            [ ( "(+)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "(*)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "(-)"         , tVar kTyp "a" `tArr` tVar kTyp "a" `tArr` tVar kTyp "a" )
            , ( "fromInteger" , tInteger `tArr` tVar kTyp "a" )
            ]
        -- Instances
        , [ ClassInfo (InClass "Num" tInt) [] 
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(+)") )
            , ( "(*)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(*)") )
            , ( "(-)"         , Ast (varExpr (TypeInfo () (tInt `tArr` tInt `tArr` tInt) []) "@Int.(-)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInt) []) "@Int.fromInteger") )
            ]
          , ClassInfo (InClass "Num" tInteger) [] 
            [ ( "(+)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(+)") )
            , ( "(*)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(*)") )
            , ( "(-)"         , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger `tArr` tInteger) []) "@Integer.(-)") )
            , ( "fromInteger" , Ast (varExpr (TypeInfo () (tInteger `tArr` tInteger) []) "@Integer.id") )
            ]
          ]
        )
      )
    ]

testConstructorEnv :: ConstructorEnv
testConstructorEnv = constructorEnv
    [ ("Some"     , ( ["Some", "None"], 1 ))
    , ("None"     , ( ["Some", "None"], 0 ))
    , ("Zero"     , ( ["Zero", "Succ"], 0 ))
    , ("Succ"     , ( ["Zero", "Succ"], 1 ))
    , ("Leaf"     , ( ["Leaf", "Node"], 0 ))
    , ("Node"     , ( ["Leaf", "Node"], 3 ))
    , ("Leaf'"    , ( ["Leaf'", "Node'"], 0 ))
    , ("Node'"    , ( ["Leaf'", "Node'"], 5 ))
    , ("[]"       , ( ["[]", "(::)"], 0 ))
    , ("(::)"     , ( ["[]", "(::)"], 2 ))
    , ("(,)"      , ( ["(,)"], 2 ))
    , ("Foo"      , ( ["Foo"], 2 ))
    , ("#"        , ( ["#"], 1 ))
    , ("{}"       , ( ["{}"], 0 ))
    , ("Cons'"    , ( ["Nil'", "Cons'"], 3 ))
    , ("Nil'"     , ( ["Nil'", "Cons'"], 0 ))
    ]

testEvalEnv :: ValueEnv Eval
testEvalEnv = Env.fromList 
    [ -- ( "(,)" , constructor "(,)" 2 )
      ( "_#"  , fromJust (evalExpr (cLam "?0" (cPat (cVar "?0") [(["#", "?1"], cVar "?1")])) mempty) ) 
    , ( "(.)" , fromJust (evalExpr (cLam "f" (cLam "x" (cApp [cVar "f", cVar "x"]))) mempty) )
--    , ( "fn1" , fromJust (evalExpr (cLam "?0" (cLam "?1" (cApp [cVar "@Integer.(+)", cVar "?0", cVar "?1"]))) mempty) )
    ]
