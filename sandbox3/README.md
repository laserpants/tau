# tau

[-] Exhaustive patterns check
[-] Or-patterns
[-] let [a, b] = [1,2] in a
[-] Pr. printer ()
[-] Tests

let f (Some a) b = a in f (Some 42) ()

let map f xs = fix g = fun [] => [] | (x :: xs) => f x :: g xs in g xs in map (\x => x + 1) [1,2,3,4]

let
  map f xs = fix
    g = fun
      | []      => []
      | x :: xs => f x :: g xs
    in
      g xs
  in
    map (\x => x + 1) ([1, 2, 3, 4])


map : forall a b f. (Functor f) => (a -> b) -> f a -> f b

map : forall a b. (a -> b) -> List a -> List b
map f xs = fix
  g = fun
    | []      => []
    | x :: xs => f x :: g xs
  in
    g xs

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


