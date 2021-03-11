
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
