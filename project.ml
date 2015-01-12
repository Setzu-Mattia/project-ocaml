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
      | Fun of (ide list) * exp
      | Apply of exp * exp list;;

(*************************** Types  ******************************)
(*****************************************************************)
  
type generic = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z;;

  
type typ = 
    Int 
  | Bool
  | Char
  | List of typ
  | Fun of typ list * typ
  | Gen of generic;;


(************************ Environment ****************************)
(*****************************************************************)

(* Values stored in the environment and the invornment. *)
(* Deep binding policy implies a closure for functions, ence the
constructor

    DFun of ide list * environment * body

wich stands for

    DFun (formal parameters,environment closure)

 *)
exception NameAlreadyDefined of ide;;
  
type envVal =
    Unbound
  | DConst of exp * typ
  | DVar of loc * typ
  | DFun of ide list * typ list * env * exp
and
env = Env of (ide -> envVal);;
  
let emptyEnv = Env (fun x -> Unbound);;
  
let bind (Env d) (x, v) =
  match v, d x with
    _, Unbound -> Env(fun x' -> if x' = x then v
				else d x')
  | _, _ -> raise (NameAlreadyDefined(x))
;;
  
(* Always overwrite a name binding *)
let strongBind (Env d) (x,v) =
  Env (fun x' -> if x' = x then v
		 else d x');;
  
let applyEnv (Env d) x =
  d x
;;

  
(*************************** Memory ******************************)
(*****************************************************************)

(* Actual memory implementation  *)
type memFun = (loc -> exp);;

(* 2nd parameter indexes the last memory location  *)
type mem = Mem of (memFun * loc);;
  
let emptyMem = Mem ((fun l -> Empty), 0);;

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
exception DivisionByZero of exp;;
exception WrongParametersNumber of (exp * typ) list;;
exception WrongParameters;;
exception WrongParametersType of exp;;

  
(* Single expressions' semantics are defined in the following functions.
Type check is handled in the sem function. *)
  
let semprod (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) -> Eint (a' * b');;

  
let semsum (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) -> Eint (a' + b');;

  
let semdiff (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) -> Eint (a' - b');;

  
let semmod (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) when b' != 0 -> Eint (a' mod b')
  | (Eint (a'), Int), (Eint (b'), Int) when b' = 0 -> raise (DivisionByZero(Eint(b')));;

  
let semdiv (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) when b' != 0 -> Eint (a' / b')
  | (Eint (a'), Int), (Eint (b'), Int) when b' = 0 -> raise (DivisionByZero(Eint(b')));;

  
let semlessint (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) when a' < b'  -> Ebool (a' < b');;


let semeqint (a, b) =
  match a, b with
    (Eint (a'), Int), (Eint (b'), Int) -> Ebool (a' = b');;

  
let semiszero a =
  match a with
    (Eint (n), Int) -> Ebool (n = 0);;

  
let semlesschar (a, b) =
  match a, b with
    (Echar(a'), Char), (Echar (b'), Char) -> Ebool (a' = b');;

  
let semeqchar (a, b) =
  match a, b with
    (Echar(a'), Char), (Echar(b'), Char) -> Ebool (a' = b');;

  
let semor (a, b) =
  match a, b with
    (Ebool(b1), Bool), (Ebool(b2), Bool) -> Ebool (b1 || b2);;

  
let semand (a, b) =
  match a, b with
    (Ebool(b1), Bool), (Ebool(b2), Bool) -> Ebool (b1 && b2);;

  
let semnot b =
  match b with
    (Ebool(b'), Bool) -> Ebool (not b');;      
  
  
(* Function local environment builder. Defined in the semantics section because it
follows an eager evaluation policy, ence it needs the sem function. *)
let rec typeCheck forParTypList actParList =
  let combTypes = List.combine actParList forParTypList in
  List.fold_right (fun ((actParVal,actParTyp), forParTyp) b -> if (actParTyp = forParTyp) then true && b
							       else raise (WrongParametersType(actParVal))) combTypes true
  and
    
  buildLocEnvAnon actPar forParIde delta =
    if List.length actPar != List.length forParIde then raise (WrongParametersNumber(actPar))
    else let combIdeAndVal = List.combine forParIde actPar in
	 List.fold_right (fun (forParIde,(actParVal,actParTyp)) b -> strongBind b (forParIde,DConst(actParVal,actParTyp))) combIdeAndVal delta
			 
  and   

    buildLocEnvDen actPar forParIde forParTyp delta =
    if List.length forParIde != List.length actPar then raise (WrongParametersNumber(actPar))
    else let typList = List.combine forParTyp actPar in
	 let typeMatch = List.fold_right (fun (forParTyp,(actParVal,actParTyp)) b -> if forParTyp = actParTyp then b
										     else raise(WrongParametersType(actParVal))) typList true in
	 if typeMatch then buildLocEnvAnon actPar forParIde delta
	 else raise WrongParameters
  
  and   
    
 sem expr delta =
    match expr with
      Den(x) -> let xVal = applyEnv delta x in (match xVal with
						 DConst(v,t) -> (v,t)
					       | DFun (forPar,parTyp,rho,body) -> (body,type_inf body rho))
  | Eint (a) -> (Eint (a), Int)
  | Ebool (b) -> (Ebool (b), Bool)
  | Echar (c) -> (Echar (c), Char)
  | Prod (a, b) when (type_inf a delta = Int)
		     && (type_inf b delta = Int) -> (semprod (sem a delta, sem b delta), Int)
  | Sum (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> (semsum (sem a delta, sem b delta), Int)
  | Diff (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> (semdiff (sem a delta, sem b delta), Int)
  | Mod (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> (semmod (sem a delta, sem b delta), Int)
  | Div (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> (semdiv (sem a delta, sem b delta), Int)
  | Lessint (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> (semlessint (sem a delta, sem b delta), Bool)
  | Eqint (a, b) when type_inf a delta = Int
		     && type_inf b delta = Int -> (semeqint (sem a delta, sem b delta), Bool)
  | Iszero (a) when type_inf a delta = Int -> (semiszero (sem a delta), Bool)
  | Lesschar (a, b) when type_inf a delta = Char
		     && type_inf b delta = Char-> (semlesschar (sem a delta, sem b delta), Bool)
  | Eqchar (a, b) when type_inf a delta = Char
		     && type_inf b delta = Char -> (semeqchar (sem a delta, sem b delta), Bool)
  | Or (b1, b2) when type_inf b1 delta = Bool
		     && type_inf b2 delta = Bool -> (semor (sem b1 delta, sem b2 delta), Bool)
  | And (b1, b2) when type_inf b1 delta = Bool
		     && type_inf b2 delta = Bool -> (semand(sem b1 delta, sem b2 delta), Bool)
  | Not (b) when type_inf b delta = Bool -> (semnot (sem b delta), Int)
  | Ifthenelse (b, c0, c1) when sem b delta = (Ebool(true), Bool)
				&& type_inf c0 delta = type_inf c1 delta -> sem c0 delta
  | Ifthenelse (b, c0, c1) when sem b delta = (Ebool(false), Bool)
				&& type_inf c0 delta = type_inf c1 delta -> sem c1 delta
  | Apply (Fun(forParIde,body), actPar') -> let actPar = List.fold_right (fun a b -> (sem a delta) :: b) actPar' [] in
					    let delta' = buildLocEnvAnon actPar forParIde delta in
					    sem body delta'
  | Apply (Den(f),actPar) -> match applyEnv delta f with
			       DFun (forParIde,forParTyp,rho,body) -> let actPar = List.fold_right (fun a b -> (sem a delta) :: b) actPar [] in
								      let delta' = buildLocEnvDen actPar forParIde forParTyp delta in
								      sem body delta'
  | _ -> raise (WrongType expr)
;;

sem (Apply(Fun(["a"],Den("a")),[Eint(1)])) emptyEnv;;
  
(* An sub-environment for types only. *)
type ideTypInf = Inf of (ide -> typ);;
type parInf = ParTyp of (ideTypInf * generic);;
  
exception ArgumentsOverflow;;
exception ParameterTypeAmbiguity of ide * typ * typ;;
exception TypeAmbiguity of typ * typ;;
exception ParameterNotFound of ide;;

let nextGen x =
  match x with
    A -> B | B -> C | C -> D | D -> E | E -> F
    | F -> G | G -> H | H -> I | I -> J | J -> K
    | K -> L | L -> M | M -> N | N -> O | O -> P
    | P -> Q | Q -> R | R -> S | S -> T | T -> U
    | U -> V | V -> W | W -> X | X -> Y | Y -> Z
    | Z -> raise (ArgumentsOverflow)
;;

let emptyTypes = Inf (fun identifier -> raise(ParameterNotFound(identifier)));;

(* Try and get the type: if not assigned yet, ideTypInf will raise
an exception, so we can add the new type. Otherwise, the parameter
type already has been defined, and we shall raise an exception. *)

(* If id has no defined type I can add one.
Otherwise raise an exception. *)
(* Se c'è già (non lancia eccezione), allora lancia eccezione.
   Altrimenti bind.  *)
let bindTypPar (Inf(f)) id typ =
  let isTyped = try let t = f id in true
		with e -> false in
  if isTyped then (Inf(f))
  else Inf(fun id' -> if id' = id then typ
		      else f id')
;;
  
let applyTypPar (Inf(f)) id =
  f id
;;

exception Temp of (exp list * typ * typ);;
exception Bod of ide list;;
  
let rec type_inf_body f body par' delta t =
  match body, t with
    Den(p), _ -> (bindTypPar f p t, par')
  | Sum(a,b), Int | Prod(a,b), Int | Div(a,b), Int | Diff(a,b), Int | Mod(a,b), Int
  | Sum(a,b), Gen(_) | Prod(a,b), Gen(_) | Div(a,b), Gen(_) | Diff(a,b), Gen(_) | Mod(a,b), Gen(_) ->
										   let (f',lg) = type_inf_body f a par' delta Int in
  										   type_inf_body f' b par' delta Int
  | Iszero(x), Bool | Iszero(x), Gen(_) ->
		       type_inf_body f x par' delta Bool
  | Lesschar(a,b), Bool | Eqchar(a,b), Bool
  | Lesschar(a,b), Gen(_) | Eqchar(a,b), Gen(_) ->
			     let (f',lg) = type_inf_body f a par' delta Char in
  			     type_inf_body f' b par' delta Char
  | And(a,b), Bool | Or(a,b), Bool
  | And(a,b), Gen(_) | Or(a,b), Gen(_) ->
			let (f',lg) = type_inf_body f a par' delta Bool in
  			type_inf_body f' b par' delta Bool
  | Not(b), Bool | Not(b), Gen(_) ->
		    type_inf_body f b par' delta Bool
  | Ifthenelse(b,c0,c1), Gen(_) ->
     let (f',lg) = type_inf_body f b par' delta (Gen(A)) in
     let (f'',lg') = type_inf_body f' c0 par' delta (Gen(A)) in
     type_inf_body f'' c1 par' delta (Gen(A))
  | Fun(forPar,body'), _ ->
     type_inf_body f body' (par' @ forPar) delta (Gen(A))
  | Apply(Fun(forPar,body'),actPar), t -> (let (eval,t') = sem body delta in
					  match t, t = t' with
					    Gen(_), _ | _, true -> type_inf_body f body' (par' @ forPar) delta t'
					    | _, _ -> raise(Temp([body],t,t')))
  | Apply(foo,actPar), t -> raise(Temp([foo],t,t))
  | Sum(a,b), _ | Prod(a,b), _ | Div(a,b), _
  | Diff(a,b), _ | Mod(a,b), _  -> raise(Temp([a;b],Int,t))	
  | Iszero(x), _ | Iszero(x), _ -> raise(Temp([x],Bool,t))
  | Lesschar(a,b), _ | Eqchar(a,b), _ -> raise(Temp([a;b],Char,t))
  | And(a,b), _ | Or(a,b), _ -> raise(Temp([a;b],Bool,t))
  | Not(b), _ -> raise(Temp([b],Bool,t))
  | _ -> (f, par')

  and


type_inf_par foo delta types =
  let type_inf_par' foo delta types gen =
    match foo with
      Empty -> failwith "empty body"
    | Fun(forPar,body) -> let (types',forPar') = type_inf_body types body forPar delta (Gen(A)) in
			   let rec parTypes par gen l =
			     match par with
			       [] -> l
			     | hd::tl -> (try let t = applyTypPar types' hd in
					      parTypes tl gen (l @ [(hd,t)])
					  with e -> let gen' = nextGen gen in
						    parTypes tl gen' (l @ [(hd,Gen(gen))]))
			   in parTypes (forPar @ forPar') A []
    | _ -> failwith "s"
  in (type_inf_par' foo delta types A)

;;
