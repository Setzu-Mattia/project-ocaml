let p = type_inf_par (Fun(["a";"b";"c";"d";"e";"f";"g";"h";"i";"j"],
			  Diff(Sum(Den("a"),Den("c")),Mod(Div(Den("j"),Den("g")),Prod(Den("f"),Den("h")))))) emptyEnv;;


let f = match p with
    [(i,f)] -> f;;

applyTypPar f "a";;
applyTypPar f "b";;
applyTypPar f "c";;
applyTypPar f "d";;
applyTypPar f "e";;
applyTypPar f "f";;
applyTypPar f "g";;
applyTypPar f "h";;
applyTypPar f "i";;
applyTypPar f "j";;
