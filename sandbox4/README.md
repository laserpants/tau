
 (づ｡◕‿‿◕｡)づ

% modulo operator
// (integer div)
++ 
xor



(//) : (ToInteger n) => n -> n -> n


let withDefault default = 
  fun 
    | None       => default 
    | Some value => value 
  in 
    let head = 
      fun 
        | []     => None 
        | x :: _ => Some x 
      in 
        [].head <?> 0


let withDefault default = \None => default | Some value => value 
  in let head = \[] => None | x :: _ => Some x 
    in [].head ? 0

withDefault default = fun
  | None       => default 
  | Some value => value 


withDefault default = \None => default | Some value => value 
  in let head = \[] => None | x :: _ => Some x 
    in [].head ? 0


(\1 or 2 or 3 as x :: _ => 1 | _ => 0) (2 :: []) 

(\[1 or 2 or 3 as x] => 1 | _ => 0) (2 :: []) 


(\(1 or 2) as x => x) 1

---> 

  | 1 as x => x
  | 2 as x => x


(\1 or 2 => 1) 1
    -- works

(\1 or 2 :: _ => 1) [1]
    -- also works

(\[1 or 2] => 1) [1]



(\[_ as x] => x) [1]

(\_ as x => x) 5

(\[4] as x => [5] | _ => [100]) [43]

