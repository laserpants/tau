# tau

<!--

Tau.Lang

Tau.Lang.Expr
Tau.Lang.Expr.Data
Tau.Lang.Expr.Code

Tau.Lang.Type
Tau.Lang.Type.Data
Tau.Lang.Type.Code

Tau.Lang.Core

Tau.Comp
Tau.Comp.Prog
Tau.Comp.Tree

Tau.Comp.TypeInference
Tau.Comp.Unification
Tau.Comp.Pipeline

Tau.Util

Tau.Eval





let
  fn
    | ("foo", Some(y)) 
        when(y == 1)    => 1
      , when(y == 2)    => 2 
      , otherwise       => 4
    | (_, None)         => 0 : Int
    | (_, _)            => 999 : Int
  in
    fn( "baz"
      , Some(2 : Int) )


let
  fn
    | ("foo", Some(y)) 
        when(y == 1) = 1
      , when(y == 2) = 2 
      , otherwise    = 4
    | (_, None)      = 0 : Int
    | (_, _)         = 999 : Int
  in
    fn( "baz"
      , Some(2 : Int) )


https://hackage.haskell.org/package/numhask



nat
int
bigint
float
double
bool
unit
char
string

-->
