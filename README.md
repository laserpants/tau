# temp

https://stackoverflow.com/questions/38462563/how-to-work-with-ast-with-cofree-annotation


  let fun =
    match xs
      | [1,2,3] => True
      | []      => True
      | _       => False

  let fun =
    match xs with
      | [1,2,3] => True
      | []      => True
      | _       => False

  let fun =
    match xs with [1,2,3] => True | [] => True | _ => False


  let fun =
    \match
      | [1,2,3] => True
      | []      => True
      | _       => False


  let fun =
    \match
      | [1,2,3] => True
      | []      => True
      | _       => False

