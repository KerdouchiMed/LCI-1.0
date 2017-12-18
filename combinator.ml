let index = ref 0
let var_name name = let () = index := !index + 1 in (Lambda.getGrec (!index)) 
type cl_terme =
	  Variable of string
	| Application of cl_terme * cl_terme
	| Abstract of string * cl_terme
	| K
	| S
	| I
	| C
	| B

let rec toStringCl terme = match terme with
	| Variable x -> x
	| S -> "S"
	| K -> "K"
	| I -> "I"
	| C -> "C"
	| B -> "B"
	| Application (m, Variable x) -> (toStringCl m) ^ " " ^ x
	| Application (m, S) -> (toStringCl m) ^ " S"
	| Application (m, K) -> (toStringCl m) ^ " K"
	| Application (m, I) -> (toStringCl m) ^ " I"
	| Application (m, B) -> (toStringCl m) ^ " B"
	| Application (m, C) -> (toStringCl m) ^ " C"
	| Application (m, n) -> (toStringCl m) ^ " (" ^ (toStringCl n) ^ ")"
	| Abstract(x, m) -> "(\206\187" ^ x ^ "." ^ (toStringCl m) ^ ")"

let rec toCl arbre = 
	match arbre with
	| Global.Var x -> Variable x
	| Global.App (m, n) -> Application ((toCl m), (toCl n))
	| Global.Abs (x, m) -> Abstract (x, toCl m)
	| Global.CInt n -> toCl (Lambda.ofInt n)

let rec libre v arbre = 
	match arbre with
	|Variable x -> if x = v then true else false
	|Application (m, n) -> (libre v m) || (libre v n)
	|Abstract(a, m) -> if a = v then false else libre v m
	|_ -> false


let rec convert arbre = 
	match arbre with
	| K -> K
	| S -> S
	| I -> I
	| B -> B
	| C -> C
	| Variable x -> Variable x
	| Application (m, n) -> Application (convert m, convert n)
	| Abstract (x, Variable a) -> if x = a then I else Application (K, Variable a)
	| Abstract (x, Abstract(y, Variable a)) -> if a = x then K else if a = y then Application (K, I) else Application (Application (S, Application(K, K)), Application (K, Variable a))    
	| Abstract (x,Abstract(y,Abstract(z ,Application(Application(a,b),Application(c,d))))) when (a=(Variable x) && b=(Variable z) && c=(Variable y) && d=(Variable z)) -> S
	| Abstract (x, Application (m, n)) -> 
    		if (libre x m) && (libre x n) then 
    			Application (Application (S, convert (Abstract(x, convert m))), convert (Abstract(x, convert n)))
    		else if not (libre x m) && libre x n then
    			Application ((Application (B, convert m)), convert (Abstract(x, convert n)))
			else if libre x m && not (libre x n) then
				Application ((Application (C, convert (Abstract(x, convert m)))), convert n)
			else
				Application (K, Application(convert m, convert n))
	| Abstract (x, K) -> Application (K, K)
	| Abstract (x, S) -> Application (K, S)
	| Abstract (x, I) -> Application (K, I)
	| Abstract (x, C) -> Application (K, C)
	| Abstract (x, B) -> Application (K, B)
	| Abstract (x, m) -> convert (Abstract(x, convert m))



let cl_make arbre  =  convert(toCl arbre)


 let rec reduce_cl term = 

      match term with 
      |Variable x -> Variable x
      |Application (I , x) -> reduce_cl x
      |Application(Application (K,x),y) -> reduce_cl x
      |Application(Application(Application(S, a), b), c) -> reduce_cl (Application(Application(a,c), Application(b,c)))
      |Application(Application(Application(B, a), b), c) -> reduce_cl (Application(a, Application(b, c)))
      |Application(Application(Application(C, a), b), c) -> reduce_cl (Application(Application(a, c), b))
      |Application (m,n)-> let rm = reduce_cl m in if rm = m then 
		                                            Application(m, reduce_cl n) 
		                                       else reduce_cl (Application(rm, n))
      |K -> K
      |S -> S
      |I -> I
      |B -> B
      |C -> C
      |a -> a

(*
	let pv = reduce_cl term in 	if pv = term then term else reduce_cl (pv)

let rec reduce_cl term = 

		if reduce_cl term = term then term else reduce_cl (reduce_cl term)
*)
let rec isAppNumber a b n = 
	match n with
	| Variable x -> if x = b then true else false
	| Application(Variable x, m) -> if x = a then isAppNumber  a b m else false
	| _ -> false
let isNumber n = 
	match n with
	| Abstract(x, Abstract(y, m)) -> isAppNumber x y m
	| _ -> false


let rec getAppNumber n = 
	match n with
	| Abstract(a, Abstract(b, m)) -> m
	| _ -> Variable ""

let rec getNumber n = 
	match n with
	| Variable x -> 0
	| Application(a, b) -> 1 + getNumber b
	| _ -> 0

let rec cl_to_lc2 arbre = 
	let x = var_name "x" in
	let y = var_name "y" in
	let z = var_name "z" in
	match arbre with
	| Variable a -> Variable a
	| Application(Application(S, a), b) -> Abstract(z, reduce_cl (Application(Application(a, Variable z), Application(b, Variable z))))
	| Application(Application(B, a), b) -> Abstract(z, reduce_cl (Application(a, Application(b, Variable z))))
	| Application(Application(C, a), b) -> Abstract(z, reduce_cl (Application(Application(a, Variable z), b)))
	| Application(S, a) -> Abstract(y, Abstract(z, reduce_cl (Application(Application(a, Variable z), Application(Variable y, Variable z)))))
	| Application(B, a) -> Abstract(y, Abstract(z, reduce_cl (Application(a, Application(Variable y, Variable z)))))
	| Application(C, a) -> Abstract(y, Abstract(z, reduce_cl (Application(Application(a, Variable z), Variable y))))
	| Application(K, a) -> Abstract(y, reduce_cl a)
	| I -> Abstract(x, Variable x)
	| S -> Abstract(x, Abstract(y, Abstract(z, Application(Application(Variable x, Variable z), Application(Variable y, Variable z)))))
	| B -> Abstract(x, Abstract(y, Abstract(z, Application(Variable x, Application(Variable y, Variable z)))))
	| C -> Abstract(x, Abstract(y, Abstract(z, Application(Application(Variable x, Variable z), Variable y))))
	| K -> Abstract(x, Abstract(y, Variable x))
	| Application (a, b) -> Application((cl_to_lc2 a), (cl_to_lc2 b))
	| Abstract(x, m) -> Abstract(x, cl_to_lc2 (reduce_cl m))

let cl_to_lc arbre = 
  let () = index := (-1) in cl_to_lc2 arbre

let rec cl_to_purelc arbre = 
	match arbre with
	| Variable a -> Global.Var a
	| Application(a, b) -> Global.App(cl_to_purelc a, cl_to_purelc b)
	| Abstract(x, m) -> Global.Abs(x, cl_to_purelc m)	
	| a -> Global.Var "Erreur"
	
let rec forme_normal arbre = 
	if cl_to_lc arbre = arbre then arbre else 
	 (forme_normal (cl_to_lc arbre))

(*let linkedVars = ref [] 

let rec getLinkedVars arbre = 
	match arbre with
	| Variable x ->  if x.[0] = '#' then if List.mem_assoc x !linkedVars then Variable (List.assoc x !linkedVars) else 
		let () = begin linkedVars := (x, "#"^(string_of_int !i))::(!linkedVars); i := !i + 1 end in Variable ("#"^(string_of_int (!i-1))) else Variable x
	| Application (m, n) -> Application(getLinkedVars m, getLinkedVars n)
	| Abstract(x, m) -> Abstract( (if List.mem_assoc x !linkedVars then 
										List.assoc x !linkedVars else 
											let () = begin linkedVars := (x, "#"^(string_of_int !i))::(!linkedVars); i := !i + 1 end in "#"^(string_of_int (!i - 1)))
											, getLinkedVars m)
	| a -> a*)

let get_final arbre =
	forme_normal (reduce_cl arbre)





let print_cl_reduce term = 
	let x= (get_final (cl_make (term))) in 
	if isNumber (x)  
	then string_of_int (getNumber (getAppNumber(x)))
	else 
        toStringCl ((x))