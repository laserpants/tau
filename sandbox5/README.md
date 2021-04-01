

reverse 
  | (Some x, y) = x + y
  | (_     , _) = 0




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


add(x, y) = x + y

force() = yes

run(x, y) = doStuffWith(x)


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

fun(x) = x + 1

someFun(Some x, y, z) =
  match (x, y, z) with
    | (Some xx, _, _)
        when x x > 3  => xx
        when p        => 1
    | (_, _, _)       => 0

  match (x, y) with
    | (1, x) or (x, 1) 
        when x /= 0 => x
        otherwise   => 0
    | _ => 100


someValue = 5

someFun of () = Yup

someFun of (x, y) = x + y

baz of (x, y) = x + y

