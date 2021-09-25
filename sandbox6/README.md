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

Tau.Tech
Tau.Tech.Compiler

Tau.Util
Tau.Util.Env

Tau.Eval

Tau.Libs

Tau.Magic





let
  fn
    | ("foo", Some(y))
        when(y == 1)    = 1
      , when(y == 2)    = 2
      , otherwise       = 4
    | (_, None)         = 0 : Int
    | (_, _)            = 999 : Int
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
        | succ(m) = go(succ'(m, nat'(go, m)))
        | zero    = go(zero'))
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
        | succ(m) = go(succ!(m, nat!(go, m)))
        | zero    = go(zero!))
  in
    let
      factorial(n) =
        n.nat!( zero! =>
                  succ(zero)
              | succ!(m, x) =>
                  succ(m) * x )
      in
        factorial(3)



factorial : nat -> nat
factorial(n) =
  fold n as
    | zero         = 1
    | succ(m), val = succ(m) * val


-- proposal:
factorial(n) : nat -> nat =
  fold n as
    | zero         = 1
    | succ(m), val = succ(m) * val




headSize
  : (Ord a)
    => a
    -> Option string
headSize
  | x :: xs
      when(x > 100) = Some("L")
    , when(x > 10)  = Some("M")
    , otherwise     = Some("S")
  | _               = None


-- proposal:
headSize (Ord a) : a -> Option string
  | x :: xs
      when(x > 100) = Some("L")
    , when(x > 10)  = Some("M")
    , otherwise     = Some("S")
  | _               = None


-- proposal:
headSize : (Ord a) => a -> Option string
  | x :: xs
      when(x > 100) = Some("L")
    , when(x > 10)  = Some("M")
    , otherwise     = Some("S")
  | _               = None




headSize
  : (Ord a)
  => a
  -> Option string
headSize
  | x :: xs
      when(x > 100) = Some("L")
    , when(x > 10)  = Some("M")
    , otherwise     = Some("S")
  | _               = None



map : (a -> b) -> List a -> List b
map(f, xs) = xs.List'(Nil' => [] | Cons'(y, _, ys) => f(y) :: ys)


map : (a -> b) -> List a -> List b
map(f, xs) =
  fold xs as
    | []           = []
    | (y :: _), ys = f(y) :: ys


-- proposal:
map(f, xs) { (Functor f) : (a -> b) -> f a -> f b } =
  fold xs as
    | []           = []
    | (y :: _), ys = f(y) :: ys


-- proposal:
map(f, xs) oftype (Functor f) : (a -> b) -> f a -> f b =
  fold xs as
    | []           = []
    | (y :: _), ys = f(y) :: ys



-- proposal:
map(f, xs) : (Functor f) => (a -> b) -> f a -> f b =
  fold xs as
    | []           = []
    | (y :: _), ys = f(y) :: ys


-- proposal:
map(f, xs) 
  : (Functor f) => (a -> b) -> f a -> f b 
  = fold xs as
    | []           = []
    | (y :: _), ys = f(y) :: ys






fix
  List' =
    ((go, ys) =>
      match ys with
        | x :: xs = go(Cons'(x, xs, List'(go, xs)))
        | []      = go(Nil'))
  in
    let
      map(f, xs) =
        xs.List'( Nil' => []
                | Cons'(y, _, ys) => f(y) :: ys )
      in
        [1, 2, 3, 4].map(x => x + 1)




isZero : nat -> bool
isZero
  | zero = true
  | _    = false

fourIsZero : bool
fourIsZero = 4.isZero


fourIsZero : bool =
  4.isZero




match (x, y) with
  | (1, x)
      when(x /= 0) => x
    , otherwise    => 0
  | _              => 100

match (x, y) with
  | (1, x)
      when(x /= 0) = x
    , otherwise    = 0
  | _              = 100


cotype Stream a =
  { Head : a
  , Tail : Stream a
  }

cotype Stream a =
  ( Head : a
  , Tail : Stream a
  )

let
  s =
    !Stream( Head = 1, Tail = t )
  in
    s.Head

let
  s =
    Stream( Head = 1, Tail = t )
  in
    s.Head


enumFrom : Nat -> Stream Nat
enumFrom n = Stream
  { Head = n
  , Tail = enumFrom (Succ n)
  }

enumFrom : Nat -> Stream Nat
enumFrom n =
  Stream'((m, s) =>
    ( m + 1
    , Stream( Head = n
            , Tail = s )
    ), n)

type List a
  = Nil
  | Cons (List (Option a))

??

{#} Record
(#) Codata

type Stream a = Stream ( Head : a, Tail : Stream a )

enumFrom : nat -> Stream nat
enumFrom n =
  Stream (unfold((m, s) => (m + 1, ( Head = m, Tail = Stream s )), n))

baz : ( Head : a | r ) -> a
baz s = s.Head

baz : _ ( Head : a | r ) -> a
baz s = s.Head


baz2 : Stream a -> a
baz2 (Stream s) = s.Head


_.Head


type Stream a = Stream ( Head : a, Tail : Stream a )




-->
