

    (\x => x + 1) 4


    match isTrue with
      | True  => afsda
      | False => afsda


    \match
      | True  => afsda
      | False => afsda


    type Bool
      = True
      | False


    record User =
      { id    : Int
      , name  : String
      , email : String
      }


    user = User
      { id    = 1
      , name  = "Kevin Flynn"
      , email = "kevin@encom.com"
      }


### Record update

    { user | name = "Sam", email = "sam@encom.com" }

        ==>  { id = 1, name = "Sam", email = "sam@encom.com" }


### Keywords `get` and `set`


#### Getters

##### Format: `get <field_name>`

    get name : { a | name : t } -> t



    get name  <===>  (\user -> .name user)

    get name user        .name user

    user |> get name      user |> .name

    user.name


#### Setters

##### Format: `set <field_name>`

    set name : t -> { a | name : t } -> { a | name : t }



    set name  <===>  (\newName user -> { user | name = newName })

    set name "Anon" user

    user |> set name "Anon"

    user.name("Anon")


    user
      |> set name "Anon"
      |> set email "spam@internet.org"


    user.name("Anon").email("spam@internet.org")




    fun = \x =>
      match x with
        | True  => 1
        | False => 2


    fun = \match
      | True  => 1
      | False => 2


    type List a
        = Nil
        | Cons a (List a)


    -- Doesn't work:
    nines : List Int
    nines = Cons 9 nines


    cotype Stream a =
      { Head : a
      , Tail : Stream a
      }


    -- Works:
    fives : Stream Int
    fives =
      { Head = 5
      , Tail = fives
      }



    -- desugars to...

    type Stream a = Stream a (() -> Stream a)

    _Head : Stream a -> a
    _Tail : Stream a -> () -> Stream a



    -- or perhaps...

    type Stream a = Stream (() -> a) (() -> Stream a)

    _Head : Stream a -> () -> a
    _Tail : Stream a -> () -> Stream a


