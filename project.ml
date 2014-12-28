type ide = string;;
  
type loc = int;;

type exp = 
        Eint of int 
      | Ebool of bool 
      | Echar of char
      | Empty
      | Cons of exp * exp
      | Den of ide
      | Prod of exp * exp
      | Sum of exp * exp
      | Diff of exp * exp
      | Mod of exp * exp
      | Div of exp * exp
      | Lessint of exp * exp
      | Eqint of exp * exp
      | Iszero of exp
      | Lesschar of exp * exp
      | Eqchar of exp * exp
      | Or of exp * exp
      | And of exp * exp
      | Not of exp
      | Ifthenelse of exp * exp * exp
      | Let of (ide * exp) list * exp      
      | Fun of ide list * exp
      | Apply of exp * exp list;;

  
type generic = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z;;

  
type typ = 
    Int 
  | Bool
  | Char
  | List of typ
  | Fun of typ * typ
  | Gen of generic;;

  
let rec type_inf expr =
  match expr with
    Eint (n) -> Int
  | Ebool (b) -> Bool
  | Echar (c) -> Char
  | Cons (a1, a2) when type_inf a1 = type_inf a2 -> List (type_inf a1)
  | Prod (a, b) when type_inf a = Int
		     && type_inf b = Int -> Int
  | Sum (a, b) when type_inf a = Int
		    && type_inf b = Int -> Int
  | Diff (a, b) when type_inf a = Int
		     && type_inf b = Int -> Int
  | Mod (a, b) when type_inf a = Int
		    && type_inf b = Int -> Int
  | Div (a, b) when type_inf a = Int
		    && type_inf b = Int -> Int
  | Lessint (a, b) when type_inf a = Int
		        && type_inf b = Int -> Bool
  | Eqint (a, b) when type_inf a = Int
		      && type_inf b = Int -> Bool
  | Iszero (a) when type_inf a = Int -> Int
  | Lesschar (a, b) when type_inf a = Char
	       	         && type_inf b = Char -> Bool
  | Eqchar (a, b) when type_inf a = Char
		       && type_inf b = Char -> Bool
  | And (b1, b2) when type_inf b1 = Bool
		      && type_inf b2 = Bool -> Bool
  | Or (b1, b2) when type_inf b1 = Bool
		     && type_inf b2 = Bool -> Bool
  | Not (b) when type_inf b = Bool -> Bool
  | Ifthenelse (a,b,c) when type_inf a = Bool  -> int;;

  
let semprod (a, b) =
  match a, b with
    Eint (a'), Eint (b') -> Eint ((a') * (b'));;

  
let semsum (a, b) =
  match a, b with
    Eint (a'), Eint (b') -> Eint (a' + b');;

  
let semdiff (a, b) =
  match a, b with
    Eint (a'), Eint (b') -> Eint (a' - b');;

  
let semmod (a, b) =
  match a, b with
    Eint (a'), Eint (b') when b' != 0 -> Eint (a' mod b')
  | Eint (a'), Eint (b') when b' = 0 -> failwith "error";;

  
let semdiv (a, b) =
  match a, b with
    Eint (a'), Eint (b') when b' != 0 -> Eint (a' / b')
  | Eint (a'), Eint (b') when b' = 0 -> failwith "error";;

let semlessint (a, b) =
  match a, b with
    Eint (a'), Eint (b') when a' < b'  -> Ebool (true)
  | _  -> Ebool (false);;

let semeqint (a, b) =
  match a, b with
    Eint (a'), Eint (b') when a' = b'  -> Ebool (true)
  | _  -> Ebool (false);;

let semiszero a =
  match a with
    Eint (0) -> Ebool (true)
  | _  -> Ebool (false);;

let semlesschar (a, b) =
  match a, b with
    Echar(a'), Echar (b') -> Ebool (a' = b');;

let semeqchar (a, b) =
  match a, b with
    Echar(a'), Echar(b') -> Ebool (a' = b');;

let semor (a, b) =
  match a, b with
    Ebool(b1), Ebool(b2) -> Ebool (b1 || b2);;

let semand (a, b) =
  match a, b with
    Ebool(b1), Ebool(b2) -> Ebool (b1 && b2);;

let semnot b =
  match b with
    Ebool(b') -> Ebool (not b');;

let semifthenelse (a, b, c) =
  match a with
    Ebool(a) -> b
  | _ -> c;;
  
let rec sem expr =
  match expr with
    Empty -> Empty
  | Eint (a) -> Eint (a)
  | Ebool (b) -> Ebool (b)
  | Echar (c) -> Echar (c)
  | Prod (a, b) -> semprod (sem a, sem b)
  | Sum (a, b) -> semsum (sem a, sem b)
  | Diff (a, b) -> semdiff (sem a, sem b)
  | Mod (a, b) -> semmod (sem a, sem b)
  | Div (a, b) -> semdiv (sem a, sem b)
  | Lessint (a, b) -> semlessint (sem a, sem b)
  | Eqint (a, b) -> semeqint (sem a, sem b)
  | Iszero (a) -> semiszero (sem a)
  | Lesschar (a, b) -> semlesschar (sem a, sem b)
  | Eqchar (a, b) -> semeqchar (sem a, sem b)
  | Or (b1, b2) -> semor (sem b1, sem b2)
  | And (b1, b2) -> semand(sem b1, sem b2)
  | Not (b) -> semnot (sem b)
  | Ifthenelse(a, b, c) -> semifthenelse(sem a,sem b,sem c)
;;

Ifthenelse (Ebool(2==2),Eint(3),Eint(4));;
