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
      | Apply of exp * exp list
      | Raise of ide
      | Try of exp * ide * exp
;;

(*************************** Types  ******************************)
(*****************************************************************)
  
type generic = string;;

  
type typ = 
    Tint 
  | Tbool
  | Tchar
  | Tlist of typ
  | Tfun of typ list * typ
  | Tgen of generic;;


(************************ Environment ****************************)
(*****************************************************************)

exception NameAlreadyDefined of ide;;
  
type envVal =
    Unbound
  | DConst of exp * typ
  | DFun of ide list * typ list * env * exp
  | Exc
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


(************************** Semantics ****************************)
(*****************************************************************)

exception WrongType of exp;;
exception DivisionByZero of exp;;
exception WrongParametersNumber of (exp * typ) list;;
exception WrongParameters;;
exception WrongParametersType of exp;;

(* An sub-environment for types only. *)
type ideTypInf = Inf of (ide -> typ);;
type parInf = ParTyp of (ideTypInf * generic);;
  
exception BodyError;;
exception ParameterTypeAmbiguity of ide * typ * typ;;
exception TypeAmbiguity of exp list * typ * typ;;
exception ParameterNotFound of ide;;
exception DuplicateParameters;;

let nextLetter x =
  match x with
    "A" -> "B" | "B" -> "C" | "C" -> "D" | "D" -> "E" | "E" -> "F"
    | "F" -> "G" | "G" -> "H" | "H" -> "I" | "I" -> "J" | "J" -> "K"
    | "K" -> "L" | "L" -> "M" | "M" -> "N" | "N" -> "O" | "O" -> "P"
    | "P" -> "Q" | "Q" -> "R" | "R" -> "S" | "S" -> "T" | "T" -> "U"
    | "U" -> "V" | "V" -> "W" | "W" -> "X" | "X" -> "Y" | "Y" -> "Z"
    | "Z" -> "A"
;;
  
let nextGen lastGen =  
  let getNumber s =
  if String.length s > 1 then 
    let stringNumber = String.sub s 1 (String.length s - 1) in
    int_of_string(stringNumber)
  else 0 in
  let lastNum = getNumber lastGen in
  let lastLetter = String.make 1 (String.get lastGen 0) in
  match String.length lastGen > 1, String.make 1 (String.get lastGen 0) with
    false, "Z" -> (nextLetter "Z")^(string_of_int(lastNum + 1))
  | false, _ -> nextLetter lastLetter
  | true, "Z" -> (nextLetter "Z")^(string_of_int(lastNum + 1))
  | true, _ -> (nextLetter lastLetter)^(string_of_int(lastNum));;
    
let emptyTypes = Inf (fun identifier -> raise(ParameterNotFound(identifier)));;

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
 
let semprod (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) -> Eint (a' * b');;

  
let semsum (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) -> Eint (a' + b');;

  
let semdiff (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) -> Eint (a' - b');;

  
let semmod (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) when b' != 0 -> Eint (a' mod b')
  | (Eint (a'), Tint), (Eint (b'), Tint) when b' = 0 -> raise (DivisionByZero(Eint(b')));;

  
let semdiv (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) when b' != 0 -> Eint (a' / b')
  | (Eint (a'), Tint), (Eint (b'), Tint) when b' = 0 -> raise (DivisionByZero(Eint(b')));;

  
let semlessint (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) when a' < b'  -> Ebool (a' < b');;


let semeqint (a, b) =
  match a, b with
    (Eint (a'), Tint), (Eint (b'), Tint) -> Ebool (a' = b');;

  
let semiszero a =
  match a with
    (Eint (n), Tint) -> Ebool (n = 0);;

  
let semlesschar (a, b) =
  match a, b with
    (Echar(a'), Tchar), (Echar (b'), Tchar) -> Ebool (a' = b');;

  
let semeqchar (a, b) =
  match a, b with
    (Echar(a'), Tchar), (Echar(b'), Tchar) -> Ebool (a' = b');;

  
let semor (a, b) =
  match a, b with
    (Ebool(b1), Tbool), (Ebool(b2), Tbool) -> Ebool (b1 || b2);;

  
let semand (a, b) =
  match a, b with
    (Ebool(b1), Tbool), (Ebool(b2), Tbool) -> Ebool (b1 && b2);;

  
let semnot b =
  match b with
    (Ebool(b'), Tbool) -> Ebool (not b');;

let rec checkDupPar l =
  match l with
    [] -> false
  | hd::tl -> if List.exists (fun x -> x = hd) tl then true
	      else checkDupPar tl;;
  
let rec type_inf expr delta =
  match expr with
    Eint (n) -> Tint
  | Ebool (b) -> Tbool
  | Echar (c) -> Tchar
  | Cons (a1, a2) when (type_inf a1 delta) = (type_inf a2 delta) -> Tlist (type_inf a1 delta)
  | Prod (a, b) when type_inf a delta = Tint
         && type_inf b delta = Tint -> Tint
  | Sum (a, b) when type_inf a delta = Tint
        && type_inf b delta = Tint -> Tint
  | Diff (a, b) when type_inf a delta = Tint
         && type_inf b delta = Tint -> Tint
  | Mod (a, b) when type_inf a delta = Tint
        && type_inf b delta = Tint -> Tint
  | Div (a, b) when type_inf a delta = Tint
        && type_inf b delta= Tint -> Tint
  | Lessint (a, b) when type_inf a delta = Tint
            && type_inf b delta = Tint -> Tbool
  | Eqint (a, b) when type_inf a delta = Tint
          && type_inf b delta = Tint -> Tbool
  | Iszero (a) when type_inf a delta = Tint -> Tint
  | Lesschar (a, b) when type_inf a delta = Tchar
                   && type_inf b delta = Tchar -> Tbool
  | Eqchar (a, b) when type_inf a delta = Tchar
           && type_inf b delta = Tchar -> Tbool
  | And (b1, b2) when type_inf b1 delta = Tbool
          && type_inf b2 delta = Tbool -> Tbool
  | Or (b1, b2) when type_inf b1 delta = Tbool
         && type_inf b2 delta = Tbool -> Tbool
  | Not (b) when type_inf b delta = Tbool -> Tbool
  | Ifthenelse (b, c0, c1) when type_inf c0 delta = type_inf c1 delta -> type_inf c0 delta
  | Fun (par_l, r) -> let parTyp = type_inf_par expr delta emptyTypes in
		      let retTyp= type_inf_fun expr delta in
		      (Tfun(parTyp,retTyp))
  | Apply (f, par_list) -> let (v,t,e) = sem expr delta in
										 t
  | Den (id) -> (match applyEnv delta id with
            DConst (v, t) -> t
          | Unbound -> raise (NotDefined id))
  | _ -> raise (TypeMismatch expr)

  and

type_inf_body f body par' delta t =
  match body, t with
    Den(p), _ -> (match t, applyEnv delta p with
		    Tgen(x), DConst(_,t') ->
		    (bindTypPar f p t', par')
		  | _, _ -> (bindTypPar f p t, par'))
  | Sum(a,b), Tint | Prod(a,b), Tint | Div(a,b), Tint | Diff(a,b), Tint | Mod(a,b), Tint
  | Sum(a,b), Tgen(_) | Prod(a,b), Tgen(_) | Div(a,b), Tgen(_) | Diff(a,b), Tgen(_) | Mod(a,b), Tgen(_) ->
										   let (f',lg) = type_inf_body f a par' delta Tint in
  										   type_inf_body f' b par' delta Tint
  | Iszero(x), Tbool | Iszero(x), Tgen(_) ->
		       type_inf_body f x par' delta Tbool
  | Lesschar(a,b), Tbool | Eqchar(a,b), Tbool
  | Lesschar(a,b), Tgen(_) | Eqchar(a,b), Tgen(_) ->
			     let (f',lg) = type_inf_body f a par' delta Tchar in
  			     type_inf_body f' b par' delta Tchar
  | And(a,b), Tbool | Or(a,b), Tbool
  | And(a,b), Tgen(_) | Or(a,b), Tgen(_) ->
			let (f',lg) = type_inf_body f a par' delta Tbool in
  			type_inf_body f' b par' delta Tbool
  | Not(b), Tbool | Not(b), Tgen(_) ->
		    type_inf_body f b par' delta Tbool
  | Ifthenelse(b,c0,c1), Tgen(_) ->
     let (f',lg) = type_inf_body f b par' delta (Tgen("A")) in
     let (f'',lg') = type_inf_body f' c0 par' delta (Tgen("A")) in
     type_inf_body f'' c1 par' delta (Tgen("A"))
  | Fun(forPar,body'), _ ->
     type_inf_body f body' (par' @ forPar) delta (Tgen("A"))
  | Apply(Fun(forPar,body'),actPar), t -> (let (eval,t',delta') = sem body delta in
					  match t, t = t' with
					    Tgen(_), _ | _, true -> type_inf_body f body' (par' @ forPar) delta' t'
					    | _, _ -> raise(TypeAmbiguity([body'],t,t')))
  | Apply(foo,actPar), t -> raise(TypeAmbiguity([foo],t,t))
  | Sum(a,b), _ | Prod(a,b), _ | Div(a,b), _
  | Diff(a,b), _ | Mod(a,b), _  -> raise(TypeAmbiguity([a;b],Tint,t))	
  | Iszero(x), _ -> raise(TypeAmbiguity([x],Tbool,t))
  | Lesschar(a,b), _ | Eqchar(a,b), _ -> raise(TypeAmbiguity([a;b],Tchar,t))
  | And(a,b), _ | Or(a,b), _ -> raise(TypeAmbiguity([a;b],Tbool,t))
  | Not(b), _ -> raise(TypeAmbiguity([b],Tbool,t))
  | Ebool(_), Tint -> raise(TypeAmbiguity([body],Tint,Tbool))
  | Echar(_), Tint -> raise(TypeAmbiguity([body],Tint,Tchar))
  | Eint(_), Tbool -> raise(TypeAmbiguity([body],Tbool,Tint))
  | Echar(_), Tbool -> raise(TypeAmbiguity([body],Tbool,Tchar))
  | Eint(_), Tchar -> raise(TypeAmbiguity([body],Tchar,Tint))
  | Ebool(_), Tchar -> raise(TypeAmbiguity([body],Tchar,Tbool))
  | _ -> (f, par')

  and

type_inf_par foo delta types =
  let type_inf_par' foo delta types gen =
    match foo with
      Fun(forPar,body) -> if checkDupPar forPar then raise(DuplicateParameters)
			  else let (types',forPar') = type_inf_body types body [] delta (Tgen("A")) in
			   let rec parTypes par gen l =
			     match par with
			       [] -> l
			     | hd::tl -> (try let t = applyTypPar types' hd in
					      parTypes tl gen (l @ [t])
					  with e -> let gen' = nextGen gen in
						    parTypes tl gen' (l @ [Tgen(gen)]))
			   in parTypes (forPar @ forPar') "A" []
  in (type_inf_par' foo delta types "A")

and 
  
type_inf_fun foo delta =
  match foo with
     Fun(forPar,body) -> (try let (types,forPar') = type_inf_body emptyTypes body forPar delta (Tgen("A"))in
			     match body with
			       Sum(_,_) | Prod(_,_) | Diff(_,_) | Mod(_,_)
			     | Div(_,_) -> Tint
			     | Lessint(_,_) | Eqint(_,_) | Iszero(_) | Lesschar(_,_) | Eqchar(_,_) | Or(_,_) | And(_,_) | Not(_) -> Tbool
			     | Ifthenelse(b,c0,c1) -> type_inf_fun c0 delta
			     | Fun(forPar',body') -> type_inf_fun body delta
			     | Apply(foo,actPar) -> (match sem body delta with
						      (v,t,delta') -> t)
			     | Let(assign,clos) -> let delta' = List.fold_right (fun (id,value) b ->
																		bind b (id,(DConst(value,type_inf value delta)))) assign delta in
																match sem clos delta' with
																		(value,t,e) -> t

				with e -> raise(e))
  | Sum(_,_) | Prod(_,_) | Diff(_,_) | Mod(_,_) | Div(_,_) -> Tint
  | Lessint(_,_) | Eqint(_,_) | Iszero(_) | Lesschar(_,_) | Eqchar(_,_) | Or(_,_) | And(_,_) | Not(_) -> Tbool
  | Ifthenelse(b,c0,c1) -> type_inf c0 delta
  | Let(envAss,clos) ->
     let delta' = List.fold_right (fun (id,value) b ->
				   bind b (id,DConst(value,type_inf value delta))) envAss delta in
     type_inf_fun clos delta'
  | Apply(foo,actPar) -> type_inf_fun foo delta  
  
  and
  
typeCheck forParTypList actParList =
  let combTypes = List.combine actParList forParTypList in
  List.fold_right (fun ((actParVal,actParTyp), forParTyp) b -> if (actParTyp = forParTyp) then true && b
							       else raise (WrongParametersType(actParVal))) combTypes true
  and
    
  buildLocEnvAnon actPar forParIde delta =
    if List.length actPar != List.length forParIde then raise (WrongParametersNumber(actPar))
    else (if checkDupPar forParIde then raise(DuplicateParameters)
	  else (let combIdeAndVal = List.combine forParIde actPar in
	 List.fold_right (fun (forParIde,(actParVal,actParTyp)) b -> strongBind b (forParIde,DConst(actParVal,actParTyp))) combIdeAndVal delta))
			 
  and   

    buildLocEnvDen actPar forParIde forParTyp delta =
    if List.length forParIde != List.length actPar then raise (WrongParametersNumber(actPar))
    else (if checkDupPar forParIde then raise(DuplicateParameters) else
      let typList = List.combine forParTyp actPar in
	 let typeMatch = List.fold_right (fun (forParTyp,(actParVal,actParTyp)) b -> if forParTyp = actParTyp then b
										     else raise(WrongParametersType(actParVal))) typList true in
	 if typeMatch then buildLocEnvAnon actPar forParIde delta
	 else raise WrongParameters)
  
  and   

sem_raise ide delta =
  match applyEnv delta ide with
    Exc -> (Raise ide),(Tgen("Z")),delta
  | _ -> raise(NotDefined(ide))

and

sem_catch exprExec catchExpr ideToCatch delta =
  match exprExec with
    Raise(e) -> if e = ideToCatch then sem catchExpr delta
		else sem_raise e delta
  
  and

    
 sem expr delta =
    match expr with
      Den(x) -> let xVal = applyEnv delta x in (match xVal with
						 DConst(v,t) -> (v,t,delta)
					       | DFun (forPar,parTyp,rho,body) -> (body,type_inf body rho,delta))
    | Eint (a) -> (Eint (a), Tint, delta)
    | Ebool (b) -> (Ebool (b), Tbool, delta)
    | Echar (c) -> (Echar (c), Tchar, delta)
    | Prod (a, b) when (type_inf a delta = Tint)
		       && (type_inf b delta = Tint) -> let (v,t,d) = sem a delta in
						      let (v',t',d') = sem b delta in 
						      (semprod ((v,t), (v',t')), Tint, delta)
    | Sum (a, b) when type_inf a delta = Tint
		      && type_inf b delta = Tint -> let (v,t,d) = sem a delta in
						   let (v',t',d') = sem b delta in 
						   (semsum ((v,t), (v',t')), Tint, delta)
    | Diff (a, b) when type_inf a delta = Tint
		       && type_inf b delta = Tint -> let (v,t,d) = sem a delta in
						    let (v',t',d') = sem b delta in 
						    (semdiff ((v,t), (v',t')), Tint, delta)
    | Mod (a, b) when type_inf a delta = Tint
		      && type_inf b delta = Tint -> let (v,t,d) = sem a delta in
						   let (v',t',d') = sem b delta in 
						   (semmod ((v,t), (v',t')), Tint, delta)
    | Div (a, b) when type_inf a delta = Tint
		      && type_inf b delta = Tint -> let (v,t,d) = sem a delta in
						   let (v',t',d') = sem b delta in 
						   (semdiv ((v,t), (v',t')), Tint, delta)
    | Lessint (a, b) when type_inf a delta = Tint
			  && type_inf b delta = Tint -> let (v,t,d) = sem a delta in
						       let (v',t',d') = sem b delta in 
						       (semlessint ((v,t), (v',t')), Tint, delta)
    | Eqint (a, b) when type_inf a delta = Tint
			&& type_inf b delta = Tint -> let (v,t,d) = sem a delta in
						     let (v',t',d') = sem b delta in 
						     (semeqint ((v,t), (v',t')), Tbool, delta)
    | Iszero (a) when type_inf a delta = Tint -> let (v,t,d) = sem a delta in
						(semiszero (v,t), Tbool, delta)
    | Lesschar (a, b) when type_inf a delta = Tchar
			   && type_inf b delta = Tchar-> let (v,t,d) = sem a delta in
							let (v',t',d') = sem b delta in 
							(semlesschar ((v,t), (v',t')), Tbool, delta)
    | Eqchar (a, b) when type_inf a delta = Tchar
			 && type_inf b delta = Tchar -> let (v,t,d) = sem a delta in
						       let (v',t',d') = sem b delta in 
						       (semeqchar ((v,t), (v',t')), Tbool, delta)
    | Or (b1, b2) when type_inf b1 delta = Tbool
		       && type_inf b2 delta = Tbool -> let (v,t,d) = sem b1 delta in
						      let (v',t',d') = sem b2 delta in 
						      (semor ((v,t), (v',t')), Tbool, delta)
    | And (b1, b2) when type_inf b1 delta = Tbool
			&& type_inf b2 delta = Tbool -> let (v,t,d) = sem b1 delta in
						       let (v',t',d') = sem b2 delta in 
						       (semand ((v,t), (v',t')), Tbool, delta)
    | Not (b) when type_inf b delta = Tbool -> let (v,t,d) = sem b delta in
					      (semnot (v,t), Tbool, delta)
    | Ifthenelse (b, c0, c1) -> (match sem b delta, (type_inf c0 delta) = (type_inf c1 delta) with
				   (Ebool(true),_,_), true -> sem c0 delta
				 | _ -> raise(BodyError))
    | Ifthenelse (b, c0, c1) -> (match sem b delta, (type_inf c0 delta) = (type_inf c1 delta) with
				   (Ebool(true),_,_), true -> sem c1 delta
				 | _ -> raise(BodyError))
    | Let(assignList,clos) -> let delta' = List.fold_right (fun (id,v) b ->
							    bind b (id,(DConst(v,type_inf v delta)))) assignList delta in
			      sem clos delta'
    | Apply (Fun(forParIde,body), actPar') -> let actPar = List.fold_right (fun a b -> match sem a delta with
											 (v,t,e) -> (v,t) :: b) actPar' [] in
					      let delta' = buildLocEnvAnon actPar forParIde delta in
					      sem body delta'
    | Apply (Den(f),actPar) -> (match applyEnv delta f with
				  DFun (forParIde,forParTyp,rho,body) -> let actPar = List.fold_right (fun a b -> match sem a delta with
														    (v,t,e) -> (v,t) :: b) actPar [] in
									 let delta' = buildLocEnvDen actPar forParIde forParTyp delta in
									 sem body delta'
				| _ -> raise (WrongType expr))
    | Raise (except) -> sem_raise except delta
    | Try (tryExp,excep,catchExp) -> sem_catch tryExp catchExp excep delta


  and

    sem_lazy expr delta =
    match expr with
      Apply(Fun(forParIde,body),actPar') -> let actPar = List.fold_right (fun a b -> match sem a delta with
										      (v,t,e) -> (a,t) :: b) actPar' [] in
					   let delta' = buildLocEnvAnon actPar forParIde delta in
					   sem body delta'
    | Apply(Den(f),actPar) ->
       (match applyEnv delta f with
	  DFun (forParIde,forParTyp,rho,body) -> let actPar = List.fold_right
								(fun a b -> match sem a delta with
									      (v,t,e) -> (a,t) :: b) actPar [] in
						 let delta' = buildLocEnvDen actPar forParIde forParTyp delta in
						 sem body delta')
    | _ -> sem expr delta      
    
;;
