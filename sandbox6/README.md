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

fix
  nat' =
    ((go, n) =>
      match n with
        | succ(m) => go(succ'(m, nat'(go, m)))
        | zero    => go(zero'))
  in
    let
      factorial(n) =
        n.nat'( zero' =>
                  succ(zero)
              | succ'(m, x) =>
                  succ(m) * x )
      in
        factorial(3)


fix
  nat! =
    ((go, n) =>
      match n with
        | succ(m) => go(succ!(m, nat!(go, m)))
        | zero    => go(zero!))
  in
    let
      factorial(n) =
        n.nat!( zero! =>
                  succ(zero)
              | succ!(m, x) =>
                  succ(m) * x )
      in
        factorial(3)




headSize : (Ord a) => a -> Option string
headSize
  | x :: xs
      when(x > 100) => Some("L")
    , when(x > 10)  => Some("M")
    , otherwise     => Some("S")
  | _ => None


map : (Functor f) => (a -> b) -> f a -> f b
map(f, xs) = []


-->
