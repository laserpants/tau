# (づ｡◕‿‿◕｡)づ

## Index

- [Language overview](#language-overview)
  - [Features](#features)
  - [Basic types](#basic-types)
    - [Primitive types](#primitive-types)
    - [Functions](#functions)
    - Natural numbers (Peano arithmetic)
    - Lists
    - Tuples
    - Algebraic data types
      - `Option`
      - `Result`
    - Records
  - Syntax
    - Program layout
      - Top-level definitions
      - Keywords `where`, and `and`
    - Function application and composition
    - Control structures: `if`, `let`, etc.
    - Pattern matching with `match` and `fun`
    - Anonymous (lambda) functions 
    - Dot-syntax
    - Operators
    - Type annotations
  - Patterns
    - Variable, literal and constructor patterns
    - Lists
    - Tuples
    - Records
    - `as`-patterns
    - `or`-patterns
    - Wildcard patterns
    - `when`-guards
  - Polymorphism and type classes
    - Built-in classes
  - Recursion
    - Rationale
- Compiler
- Roadmap
- Wishlist
- Contribute
  - Code of conduct
  - Bugs and issues
  - Feature requests
- License

## Language overview

### Features

  - [Purely functional](https://en.wikipedia.org/wiki/Purely_functional_programming), strict semantics
  - Haskell-like syntax 
  - No partial functions
  - No explicit recursion
  - Type classes (single-parameter only)

### Basic types

#### Primitive types

| Type      | Values                                                                                                        | Explanation                                 |
|-----------|---------------------------------------------------------------------------------------------------------------|---------------------------------------------|
| `Void`    | No values                                                                                                     | The uninhabited type                        |
| `Unit`    | `()`                                                                                                          | Type type with exactly one value. (1 in the [algebra of types](https://codewords.recurse.com/issues/three/algebra-and-calculus-of-algebraic-data-types).) |
| `Bool`    | `True`, `False`                                                                                               |                                             |
| `Int`     | `minBound`, &hellip;, `-1`, `0`, `1`, `2`, &hellip;, `maxBound`                                               | Bounded machine integers (32 or 64 bit)     |
| `Integer` | &hellip;, `-1`, `0`, `1`, `2`, &hellip;                                                                       | Arbitrary precision integers (bigints)      |
| `Float`   | &hellip;, `6.2831855`, &hellip;                                                                               | Single precision floating point numbers     |
| `Double`  | &hellip;, `6.283185307179586`, &hellip;                                                                       | Double precision floating point numbers     |
| `Char`    | `'a'`, `'b'`, &hellip;                                                                                        |                                             |
| `String`  | &hellip;, `"bork bork bork"`, &hellip;, `"klingon"`, &hellip;                                                 |                                             |

<!--
| * `Nat`     | `0`, `1`, `2`, &hellip;, or `Zero`, `Succ Zero`, `Succ (Succ Zero)`, &hellip;                               | Natural numbers (Peano arithmetic)          |
-->

#### Functions

Function types have the form `a -> b`, where `a` is the type of the argument, and `b` is the return value's type.
The arrow operator is right-associative. [Currying](https://en.wikipedia.org/wiki/Currying#Definition) naturally allows for the formation of functions of more than one argument, so `a -> b -> c` is a function of two arguments.
Some examples of function types are `Int -> Int`, `Int -> List Int -> List Int`, and `(Int -> Int) -> Int -> Bool`.

#### Option types

```
head : forall a. List a -> Option a
head (x :: _) = Some x
head _        = None
```

```
headOr : forall a. a -> List a -> a
headOr rep xs = head xs ? rep
```

#### Natural numbers (Peano arithmetic)
#### Lists
#### Tuples
#### Algebraic data types
##### `Option`
##### `Result`
#### Records
### Syntax
#### Program layout
##### Top-level definitions
##### Keywords `where`, and `and`
#### Function application and composition
#### Control structures: `if`, `let`, etc.
#### Pattern matching with `match` and `fun`
#### Anonymous (lambda) functions 
#### Dot-syntax
#### Operators
#### Type annotations
### Patterns
#### Variable, literal and constructor patterns
#### Lists
#### Tuples
#### Records
#### `as`-patterns
#### `or`-patterns
#### Wildcard patterns
#### `when`-guards
### Polymorphism and type classes
#### Built-in classes
### Recursion
#### Rationale
## Compiler
## Roadmap
## Wishlist
## Contribute
### Code of conduct
### Bugs and issues
### Feature requests
## License






<!--

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

x = 3
  where
    y = 4 and
    z = 5 and
    a = b


fun = (\Some x when x > 100 => x + 1 | _ => 0) (Some 105)

headOrZero : List Int -> Int
headOrZero xs = xs.head ? 0
  where
    head = 
      fun 
        | []     => None 
        | x :: _ => Some x 
  and
    withDefault default = 
      fun 
        | None       => default 
        | Some value => value 


headOrZero : List Int -> Int
headOrZero xs = xs.head ? 0
  where
    head []       = None 
    head (x :: _) = Some x 
  and
    withDefault default = 
      \(Some value) => value | None => default 

fun (x :: _) 
  when x > 100 = 5 
  when x < 50  = 3 
  otherwise    = 1

fun (x :: _) = 100 
fun _        = 200


# -- keyword        let, if, where, type, etc.
# -- literal
# --    integers
# --    float
# --    ()
# -- name           x, _foo, hello, etc.
# -- constructor    List, Cons, etc.
# -- symbol         *, +, <>, =, ==, etc
# -- newline
# -- space
# -- comment

-->
