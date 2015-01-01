(* Build global environment *)
let globalEnv = emptyEnv;;
let globalEnv = bind globalEnv ("a",DConst(Echar('a'),type_inf (Echar('a')) globalEnv));;
let globalEnv = bind globalEnv ("b",DConst(Echar('b'),type_inf (Echar('b')) globalEnv));;
let globalEnv = bind globalEnv ("c",DConst(Echar('c'),type_inf (Echar('c')) globalEnv));;
let globalEnv = bind globalEnv ("d",DConst(Echar('d'),type_inf (Echar('d')) globalEnv));;

(* Build local environment *)
let localEnv = globalEnv;;
let localEnv = forceBind localEnv ("a",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("b",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("c",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("d",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("e",DConst(Echar('e'),type_inf (Echar('e')) localEnv));;
let localEnv = forceBind localEnv ("f",DConst(Echar('f'),type_inf (Echar('f')) localEnv));;
  
(* Global environment values *)
applyEnv globalEnv "a";;
applyEnv globalEnv "b";;
applyEnv globalEnv "c";;
applyEnv globalEnv "d";;
applyEnv globalEnv "e";;
applyEnv globalEnv "f";;
  
(* Local environment values *)
applyEnv localEnv "a";;
applyEnv localEnv "b";;
applyEnv localEnv "c";;
applyEnv localEnv "d";;
applyEnv localEnv "e";;
applyEnv localEnv "f";;
(* Build global environment *)
let globalEnv = emptyEnv;;
let globalEnv = bind globalEnv ("a",DConst(Echar('a'),type_inf (Echar('a')) globalEnv));;
let globalEnv = bind globalEnv ("b",DConst(Echar('b'),type_inf (Echar('b')) globalEnv));;
let globalEnv = bind globalEnv ("c",DConst(Echar('c'),type_inf (Echar('c')) globalEnv));;
let globalEnv = bind globalEnv ("d",DConst(Echar('d'),type_inf (Echar('d')) globalEnv));;

(* Build local environment *)
let localEnv = globalEnv;;
let localEnv = forceBind localEnv ("a",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("b",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("c",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("d",DConst(Echar('z'),type_inf (Echar('z')) localEnv));;
let localEnv = forceBind localEnv ("e",DConst(Echar('e'),type_inf (Echar('e')) localEnv));;
let localEnv = forceBind localEnv ("f",DConst(Echar('f'),type_inf (Echar('f')) localEnv));;
  
(* Global environment values *)
applyEnv globalEnv "a";;
applyEnv globalEnv "b";;
applyEnv globalEnv "c";;
applyEnv globalEnv "d";;
applyEnv globalEnv "e";;
applyEnv globalEnv "f";;
  
(* Local environment values *)
applyEnv localEnv "a";;
applyEnv localEnv "b";;
applyEnv localEnv "c";;
applyEnv localEnv "d";;
applyEnv localEnv "e";;
applyEnv localEnv "f";;


(**************************************************************)

  let gEnv0 = emptyEnv;;
let gEnv0 = bind gEnv0 ("a",DConst(Echar('a'),type_inf (Echar('a')) gEnv0));;
let gEnv0 = bind gEnv0 ("b",DConst(Echar('a'),type_inf (Echar('a')) gEnv0));;
let gEnv0 = bind gEnv0 ("c",DConst(Echar('a'),type_inf (Echar('a')) gEnv0));;

  
let gEnv1 = bind gEnv0 ("foo",DFun(["a";"b";"c"],emptyEnv,Empty));;
let lEnv = buildFunctionEnvironment gEnv1 "foo" [Eint(1);Sum(Eint(1),Eint(1));Sum(Eint(1),Sum(Eint(1),Eint(1)))];;

applyEnv lEnv "a";;
