

## Overview

## Language spec and implementation

### (E)BNF grammar

    https://mdkrajnak.github.io/ebnftest/
    https://www.bottlecaps.de/rr/ui

    expr 
      = var_expr
      | let_expr 
      | literal_expr

    Expr 
      = VarExpr
      | LetExpr 
      | LiteralExpr

    Name
      = #'[A-Za-z_][A-Za-z0-9_+]*'

    Prim
      = '()' 
      | ('True' | 'False')

    VarExpr
      = Name

    LetExpr     
      = 'let' 
      , Spaces 
      , LetBinding

    LetBinding
      = PatternBinding

    PatternBinding
      = Name , Spaces
      , '='  , Spaces
      , Expr , Spaces
      , 'in' , Spaces
      , Expr

    LiteralExpr 
      = Prim

    Spaces      
      = ' '+




(_ - 1)

let pred = _ - 1

match xs with
  | val x :: _ => True

match xs with
  | .x :: _ => True

match xs with
  | !x :: _ => True



let args = (5, 3)

(+)(...args)


(+)(5, 3)


let 
  ys.map(f) = e    ==>  let map(f, ys) = e


ys.length = ...

List.length = ... match this with      ==>   length(x) = match x with


add(5, _)         <==>  ^0 => add(5, ^0)

add(_, 5)         <==>  ^0 => add(^0, 5)



    EAppX [add, _, 5]

    EAppX [_, add, 5]

foo = fun
  | (2, 3) => True
  | (3, 4) => True
  | (_, _) => False


match x, y with




grok : Option Int -> Int -> Int
grok 
  | (Some x) 1 when(x > 100) = 0  
  | None     1               = 1 
  | _        _               = 2
  where
    valid = True


grok : Option(Int) -> Int -> Int


reverse 
  | (Some x, y) = x + y
  | (_     , _) = 0



incrementEach : (Functor f, Num a) => f a -> f a
incrementEach(xs) = xs.map(x => x + 1)


incrementEach(xs) = xs.map(_ + 1)


-- lambda

((Some x, y, z) => x)(Some 5, 3 2)

-- fun (1 arg)

(Some x => x | None => 0)

(function | Some x => x | None => 0)

(fun | Some x => x | None => 0)

(function
  | Some x => x 
  | None => 0)

(fun 
  | Some x => x 
  | None   => 0)

(of
  | Some x => x 
  | None   => 0)

-- Let fun

let f(x, y) = x + y

stuff((3, 4))

-- Let f = (x, y) => x + y


let f 
  | Some x 
      when x > 3  => 5
      when x <= 0 => 1
  | None          => 0


let f = fun
  | Some x 
      when x > 3 => 5
      when x < 0 => 1
  | None         => 0

let f of
  | Some x 
      when x > 3 = 5
      when x < 0 = 1
  | None         = 0



add(x, y) = x + y

force() = yes

run(x, y) = doStuffWith(x)


add : Int -> Int -> Int
add(x, y) = x + y

add : Int -> Int -> Int
add(x, y) = x + y

add5 : Int -> Int
add5 = add(5) 

add5 = add(5, _)

add5 = add(_, 5)

nope : IO ()
nope() = print("Done")

main : () -> IO ()
main() = nope ()

someFun of () = 1

someFun of 
    | x y z = x + 1
    | x z d = x + 1
  where
    x = 1
  and
    y = 2

fn of x = 1

someFun of x y z = x + 1

someFun of (x, y) = x + y

someFun(x, y) = x + y

someFun((x, y)) = x + y

fun(x) = x + 1

someFun(Some x, y, z) =
  match (x, y, z) with
    | (Some xx, _, _)
        when x x > 3  => xx
        when p        => 1
    | (_, _, _)       => 0

someFun(Some x, y, z) =
  match (x, y, z) with
    | (Some(xx), _, _)
        when(x x > 3) => xx
        when(p)       => 1
    | (_, _, _)      => 0


  match (x, y) with
    | (1, x) or (x, 1) 
        when x /= 0 => x
        otherwise   => 0
    | _ => 100


someValue = 5

someFun of () = Yup

someFun of (x, y) = x + y

baz of (x, y) = x + y


length xs 

xs.length()

length () xs


xs.map(\x => x + 1)

map (\x => x + 1) xs

foo(())



let x = fun | Some(y) => y | None => 123 in x(Some(3)) 

let x | Some(y) => y | None => 123 in x(Some(3)) 

let withDefault(val) = fun | Some(y) => y | None => val in Some(3).withDefault(5)

let withDefault(val) | Some(y) = y | None = val in Some(3).withDefault(5)


let 
  withDefault(val) 
    | Some(y) = y 
    | None    = val 
  in 
    Some(3).withDefault(5)


let 
  withDefault(val) = fun
    | Some(y) = y 
    | None    = val 
  in 
    Some(3).withDefault(5)



if z > 10 then 3 else match x with | Some(z) when(z > 10) => 1 : Int; when(z > 5) => 2 : Int; otherwise => 3 : Int | Some(z) => 2

if z > 10 
  then 
    3
  else
    match x with
      | Some(z) 
          when(z > 10) => 1 : Int
          when(z > 5)  => 2 : Int
          otherwise    => 3 : Int
      | Some(z)        => 2

foo 
  | a when(a > 3) => 1
  | _            => 0

foo 
  | (a, b) when(a > 3) => 1
  | _                 => 0

foo 
  | (a, b) 
      when(a > 3)      => 1
  | _                 => 0



foo(a, b, c) =
  match (a, b, c) with
    | (1, 1, 1) => True
    | _         => False

foo 
  | (1, 1, 1) => True
  | _         => False



foo 
  | 2 => True
  | 3 => True
  | _ => False

foo = fun
  | 2 => True
  | 3 => True
  | _ => False

foo 
  | (2, 3) => True
  | (3, 4) => True
  | (_, _) => False

foo 
  | 2, 3 => True
  | 3, 4 => True
  | _, _ => False

foo(a, b) =
  match (a, b) with
    | (2, 3) => True
    | (3, 4) => True
    | (_, _) => False

foo = fun 2
  | (2, 3) => True
  | (3, 4) => True
  | (_, _) => False

foo 
  | (2, 3) => True
  | (3, 4) => True
  | (_, _) => False


foo((a, b)) = a + b

foo(<a, b>) = a + b

<a, b>.second


createTuple(x, y) = <x, y>

replace OField ...> @#getField

semicolon


let x =
  if z > 10 
    then match x with | Some(z) when(z > 10) => 1 : Int; when(z > 5) => 2 : Int; otherwise => 3 : Int | Some(z) => 2 | None => 3
    else match x with | Some(z) when(z > 10) => 1 : Int; when(z > 5) => 2 : Int; otherwise => 3 : Int | Some(z) => 2
  in
    3

