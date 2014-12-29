let m1 = emptyMem ();;
getValue m1 0;;
getValue m1 10;;
let m2 = storeValue m1 (Eint(1),1);;
let m3 = storeValue m2 (Eint(1),1);;
let m4 = storeValue m3 (Eint(1),1);;
let m5 = storeValue m4 (Eint(1),1);;
getValue m4 1;;  
