# tau 
[-] Records, tuples and lists in exhaustive patterns check
[-] Or-patterns
[-] Pr. printer ()   -- (fun expression is wrong)
[-] Tests
[-] Type schemes

--


(fun ((Some x)) _ => None | None () => Some 0) (Some 99) ()


--

(fun ((Some x) as someX) _ => someX | None _ => Some 0) (Some 99) ()


--

(fun ((Some x) as someX) _ => someX | None _ => Some 0) None ()

--


fails:
    (fun (Some x as someX) _ => x | None _ => 0) (Some 5) ()

--

(fun (Some x) _ when x == 1 => x | None _ => 0 | _ _ => 2 ) (Some 5) ()

--

(fun (Some x) _ => x | None _ => 0) (Some 5) ()

--

let map f xs = fix mu = fun [] => [] | (x :: xs) => f x :: mu xs in mu xs in let addOne = map (\x => x + 1) in [1,2,3,4].addOne

let
  map f xs = fix
    mu = fun
      | []      => []
      | x :: xs => f x :: mu xs
    in
      mu xs
  in
    let
      addOne = map (\x => x + 1)
      in
        [1, 2, 3, 4].addOne

--

let f (Some a) b = a in f (Some 42) ()

let map f xs = fix mu = fun [] => [] | (x :: xs) => f x :: mu xs in mu xs in map (\x => x + 1) [1,2,3,4]

let
  map f xs = fix
    mu = fun
      | []      => []
      | x :: xs => f x :: mu xs
    in
      mu xs
  in
    map (\x => x + 1) [1, 2, 3, 4]


map : forall a b f. (Functor f) => (a -> b) -> f a -> f b

map : forall a b. (a -> b) -> List a -> List b
map f xs = fix
  nu = fun
    | []      => []
    | x :: xs => f x :: g xs
  in
    nu xs

--

let fact a = fix f = fun 0 => 1 | n => n * f (n - 1) in f a in fact 5

let
  fact a = fix
    f = fun 0 => 1 | n => n * (f n - 1)
    in
      f a
  in
    fact 5


--


