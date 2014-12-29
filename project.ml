type ide = string;;
type loc = int;;

(************************ Expressions  ***************************)
(*****************************************************************)
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


(*************************** Types  ******************************)
(*****************************************************************)
  
type generic = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z;;

  
type typ = 
    Int 
  | Bool
  | Char
  | List of typ
  | Fun of typ * typ
  | Gen of generic;;


(************************ Environment ****************************)
(*****************************************************************)
  
type envVal =
    Unbound
  | DConst of exp * typ
  | DVar of loc * typ
;;

type env = Env of (ide -> envVal);;

exception NameAlreadyDefined of ide;;
  
let emptyEnv = Env (fun x -> Unbound);;
  
let bind (Env d) (x, v) =
  match v, d x with
    _, Unbound -> Env(fun x' -> if x' = x then v
								else d x')
  | DConst (v', t), _ -> raise (NameAlreadyDefined x)
  | DVar (l, t), DConst (_, _) -> raise (NameAlreadyDefined x)
;;

let applyEnv (Env d) x =
  d x
;;
  
  
(*************************** Memory ******************************)
(*****************************************************************)
  
type memFun = (loc -> exp);;

type mem = Mem of (memFun * loc);;
  
let emptyMem () =
  Mem ((fun l -> Empty), 0)
;;

let storeValue m (value, size) =
  match m with
    Mem (mem_fun, l) -> Mem ((fun l' -> if l' = l then value
					else mem_fun l'),
			     l + size)
;;

let getValue m l =
  match m with
    Mem (f, l') -> f l
;;


(************************ Type system  ***************************)
(*****************************************************************)
 
exception TypeMismatch of exp;;
exception NotDefined of ide;;
 
let rec type_inf expr delta =
  match expr with
    Eint (n) -> Int
  | Ebool (b) -> Bool
  | Echar (c) -> Char
  | Cons (a1, a2) when (type_inf a1 delta) = (type_inf a2 delta) -> List (type_inf a1 delta)
  | Prod (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> Int
  | Sum (a, b) when type_inf a delta = Int
		    && type_inf b delta = Int -> Int
  | Diff (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> Int
  | Mod (a, b) when type_inf a delta = Int
		    && type_inf b delta = Int -> Int
  | Div (a, b) when type_inf a delta = Int
		    && type_inf b delta= Int -> Int
  | Lessint (a, b) when type_inf a delta = Int
		        && type_inf b delta = Int -> Bool
  | Eqint (a, b) when type_inf a delta = Int
		      && type_inf b delta = Int -> Bool
  | Iszero (a) when type_inf a delta = Int -> Int
  | Lesschar (a, b) when type_inf a delta = Char
	       	         && type_inf b delta = Char -> Bool
  | Eqchar (a, b) when type_inf a delta = Char
		       && type_inf b delta = Char -> Bool
  | And (b1, b2) when type_inf b1 delta = Bool
		      && type_inf b2 delta = Bool -> Bool
  | Or (b1, b2) when type_inf b1 delta = Bool
		     && type_inf b2 delta = Bool -> Bool
  | Not (b) when type_inf b delta = Bool -> Bool
  | Ifthenelse (b, c0, c1) when type_inf c0 delta = type_inf c1 delta -> type_inf c0 delta
  | Fun (par_l, r) -> type_inf r delta
  | Apply (f, par_list) -> type_inf f delta
  | Den (id) -> (match applyEnv delta id with
					  DConst (v, t) -> t
					| DVar (l, t) -> t
					| Unbound -> raise (NotDefined id))
  | _ -> raise (TypeMismatch expr)
;;


(************************** Semantics ****************************)
(*****************************************************************)

exception WrongType of exp;;

let semprod (a, b) =
  match a, b with
    Eint (a'), Eint (b') -> Eint (a' * b');;

  
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
    Eint (a'), Eint (b') -> Ebool (a' = b');;

let semiszero a =
  match a with
    Eint (n) -> Ebool (n = 0);;

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
  

let rec sem expr delta =
  match expr with
    Empty -> Empty
  | Eint (a) -> Eint (a)
  | Ebool (b) -> Ebool (b)
  | Echar (c) -> Echar (c)
  | Prod (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semprod (sem a delta, sem b delta)
  | Sum (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semsum (sem a delta, sem b delta)
  | Diff (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semdiff (sem a delta, sem b delta)
  | Mod (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semmod (sem a delta, sem b delta)
  | Div (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semdiv (sem a delta, sem b delta)
  | Lessint (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semlessint (sem a delta, sem b delta)
  | Eqint (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> semeqint (sem a delta, sem b delta)
  | Iszero (a) when type_inf a delta = Int -> semiszero (sem a delta)
  | Lesschar (a, b) when type_inf a delta = Char
		     && type_inf b delta = Char-> semlesschar (sem a delta, sem b delta)
  | Eqchar (a, b) when type_inf a delta = Char
		     && type_inf b delta = Char -> semeqchar (sem a delta, sem b delta)
  | Or (b1, b2) when type_inf b1 delta = Bool
		     && type_inf b2 delta = Bool -> semor (sem b1 delta, sem b2 delta)
  | And (b1, b2) when type_inf b1 delta = Bool
		     && type_inf b2 delta = Bool -> semand(sem b1 delta, sem b2 delta)
  | Not (b) when type_inf b delta = Bool -> semnot (sem b delta)
  | Ifthenelse (b, c0, c1) when sem b delta = Ebool(true)
				&& type_inf c0 delta = type_inf c1 delta -> sem c0 delta
  | Ifthenelse (b, c0, c1) when sem b delta = Ebool(false)
				&& type_inf c0 delta = type_inf c1 delta -> sem c1 delta
  | _ -> raise (WrongType expr)
;;
