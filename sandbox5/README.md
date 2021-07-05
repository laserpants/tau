

grok : Option Int -> Int -> Int
grok 
  | (Some x) 1 iff x > 100 = 0  
  | None     1             = 1 
  | _        _             = 2
  where
    valid = True



reverse 
  | (Some x, y) = x + y
  | (_     , _) = 0



incrementEach : (Functor f, Num a) => f a -> f a
incrementEach(xs) = xs.map(x => x + 1)


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

-- Let f = (x, y) => x + y


let f = function
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
        iff(x x > 3) => xx
        iff(p)       => 1
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



if z > 10 then 3 else match x with | Some(z) iff(z > 10) => 1 : Int; iff(z > 5) => 2 : Int; otherwise => 3 : Int | Some(z) => 2

if z > 10 
  then 3
  else
    match x with
      | Some(z) 
          iff(z > 10) => 1 : Int
          iff(z > 5) => 2 : Int
          otherwise => 3 : Int
      | Some(z) => 2

