# tau

[-] Exhaustive patterns check
[-] Or-patterns
[-] Pr. printer ()
[-] Tests

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


map : forall a. (Functor f) => (a -> b) -> f a -> f b
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


