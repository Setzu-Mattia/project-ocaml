let e1 = emptyEnv;;
let e2 = bind e1 ("x", (DConst(Echar('x'),Int)));;
let e3 = bind e2 ("y", (DConst(Echar('y'),Int)));;
let e4 = bind e3 ("z", (DConst(Echar('z'),Int)));;
let e5 = bind e4 ("z", (DConst(Echar('z'),Int)));;

applyEnv e1 "x";;
applyEnv e2 "x";;
applyEnv e3 "y";;
applyEnv e4 "z";;
applyEnv e5 "z";;
