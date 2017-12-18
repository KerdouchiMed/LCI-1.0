let index = ref (-1)
let var_name name = let () = index := !index + 1 in (Lambda.getGrec (!index))

type debruijn = 
	| DVar of string
	| DInt of int
	| DApp of debruijn * debruijn
	| DAbs of debruijn 

	let rec replaceDebruijn arbre x i = 
	match arbre with
	| DVar v -> if v = x then DInt i else DVar v	
	| DInt x -> DInt x
	| DApp (m, n) -> DApp(replaceDebruijn m x i, replaceDebruijn n x i)
	| DAbs m -> DAbs(replaceDebruijn m x (i + 1))

let rec deb arbre = 
	match arbre with
	| Global.Var x -> DVar x
	| Global.Abs (x, m) -> DAbs(replaceDebruijn (deb m) x 0)
	| Global.App (m, n) -> DApp (deb m, deb n)
	| a -> DVar "erreur "

let rec toStringDeb arbre =
	match arbre with
	| DVar x -> x
	| DInt x -> string_of_int x
	| DApp (m, DVar x) -> (toStringDeb m) ^ " " ^ x
	| DApp (m, DInt x) -> (toStringDeb m) ^ " " ^ (string_of_int x)
	| DApp (m, n) -> (toStringDeb m) ^ " (" ^ (toStringDeb n) ^ ")"
	| DAbs m -> "(\206\187" ^ (toStringDeb m) ^ ")" 
(*
let rec fleche term  i v = match term with 
| DVar x -> DVar x
| DInt x -> if x > i then DInt (x + v) else DInt x 
| DAbs k -> DAbs (fleche k (i + 1) v)
| DApp (m , n ) -> DApp(fleche m i v ,fleche n i v)  

let rec replaceDeb arbre a b = 
	match arbre with
	| DVar x -> DVar x
	| DInt x -> if x = a then b else DInt x
	| DAbs m -> DAbs (replaceDeb m (a + 1) (fleche b 0 1))
	| DApp (m, n) -> DApp(replaceDeb m a b, replaceDeb n a b)


let rec reduceDeb arbre = 
	match arbre with
	| DVar x -> DVar x
	| DInt x -> DInt x
	| DAbs m -> DAbs (reduceDeb m)
	| DApp (DVar x, m) -> DApp(DVar x, reduceDeb m)
	| DApp (DInt x, m) -> DApp(DInt x, reduceDeb m)
	| DApp (DAbs m, n) -> reduceDeb (fleche (replaceDeb m 0 (fleche n (-1) 1)) (-1) (-1))
	| DApp (m, n) ->   reduceDeb (DApp(reduceDeb x , reduceDeb n))

*)
(*
let isNormalDeb a = reduceDeb a = a
let reduceTermDeb a = 
	let k = ref a in
	while not (isNormalDeb !k) do
		k := reduceDeb !k
	done; !k  

(*
let reduceTermDeb a= reduceDeb a  
*)

let rec reduceTermDeb a = 
	let pv = reduceDeb a in if pv = a then a else reduceTermDeb pv 
	*)

let rec fleche term  i v = match term with 
| DVar x -> DVar x
| DInt x -> if x > i then DInt (x + v) else DInt x 
| DAbs k -> DAbs (fleche k (i + 1) v)
| DApp (m , n ) -> DApp(fleche m i v ,fleche n i v)  

let rec replaceDeb arbre a b = 
	match arbre with
	| DVar x -> DVar x
	| DInt x -> if x = a then b else DInt x
	| DAbs m -> DAbs (replaceDeb m (a + 1) (fleche b 0 1))
	| DApp (m, n) -> DApp(replaceDeb m a b, replaceDeb n a b)





let beta (DAbs u) t =
    let decalage d t =
        let rec aux_decale p = function
            | DApp(t1,t2) -> DApp(aux_decale p t1,aux_decale p t2)
            | DAbs(t) -> DAbs(aux_decale (p + 1) t)
            | DInt(i) when i < p -> DInt(i)
            | DInt(i) -> DInt(i + d)
            | DVar i -> DVar i
        in
        aux_decale 0 t
    in
    let rec aux p = function
        | DApp(u1,u2) -> DApp(aux p u1,aux p u2)
        | DAbs(v) -> DAbs(aux (p + 1) v)
        | DInt(i) when i = p -> decalage p t
        | DInt(i) when i < p -> DInt(i)
        | DInt(i) -> DInt(i - 1)
        | DVar i ->DVar i
    in
    aux 0 u ;;
    
exception Stop ;;

    let rec beta_un = function
    | DInt(_) -> raise Stop
    |DVar (_) -> raise Stop
    | DAbs(t) -> DAbs(beta_un t)
    | DApp(DAbs(u),t) -> beta (DAbs u) t
    | DApp(t1,t2) -> try DApp(beta_un t1,t2) with Stop -> DApp(t1,beta_un t2) ;;

let rec beta_reduction t =
    try beta_reduction (beta_un t)
    with Stop -> t ;;












let rec debisAppNumber n = 
	match n with
	| DInt x -> if x = 0 then true else false
	| DApp(DInt x, m) -> if x = 1 then debisAppNumber m else false
	| _ -> false
let debisNumber n = 
	match n with
	| DAbs(DAbs( m)) -> debisAppNumber  m
	| _ -> false


let rec debgetAppNumber n = 
	match n with
	| DAbs(DAbs( m)) -> m
	| _ -> DVar ""

let rec debgetNumber n = 
	match n with
	| DInt x -> 0
	| DApp(a, b) -> 1 + debgetNumber b
	| _ -> 0


let rec deb_to_lc2 arbre = 
	match arbre with
	|DVar x -> Global.Var x
	|DApp (m, n) -> Global.App (deb_to_lc2 m, deb_to_lc2 n)
	|DAbs (m) -> let x = var_name "x" in Global.Abs(x, deb_to_lc2 (replaceDeb m 0 (DVar x)))
	|_ -> Global.Var ""

let deb_to_lc arbre = 
    let () = index := -1 in deb_to_lc2 arbre

let print_deb_int term =string_of_int (debgetNumber (debgetAppNumber( term)))


let print_deb_reduce term = 
let x = beta_reduction term  in
  if (debisNumber (x))
      then  print_deb_int (x)
         else    Lambda.toString(deb_to_lc (x))
