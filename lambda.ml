open Global
open LowLevelLibrary

let index = ref 0

exception ParseErr of string
let table = [|
  "α";
  "β";
  "γ";
  "δ";
  "ε";
  "ζ";
  "η";
  "θ";
  "ι";
  "μ";
  "ξ";
  "π";
  "ρ";
  "σ";
  "τ";
  "φ";
  "ψ";
  "ω"
	    |]
let getGrec i = if i < 18 then table.(i) else (table.(i mod 18) ^ (string_of_int (i - 17)))

  
   
type instruction = 
   Exp of ((string*Global.unifTypeDef) list)*termWithInfo
  |Load of string
  |Declaration of (((string*unifTypeDef) list)*(string * termWithInfo))
  |RecDeclaration of (((string*unifTypeDef) list)*(string * termWithInfo))
	|LTD of termWithInfo
	|LTC of termWithInfo
	|DTC of termWithInfo
	|DTL of termWithInfo
	|CTL of termWithInfo
	|CTD of termWithInfo
	|Exit
	|Unit of unit

let rec getIntPur n = 
  match n with
  	|0 -> Var "x"
    |p -> App( Var "f", getIntPur (p-1))
    
let ofInt n = Abs("f", Abs("x", getIntPur n))

let rec toString terme = match terme with
  |Var x -> x
	|CInt n -> (toString (ofInt n))
  |App (m, Var x) -> (toString m) ^ " " ^ x
  |App (m, n) -> (toString m) ^ " (" ^ (toString n) ^ ")"
  |Abs (x, m) -> "(\206\187" ^ x ^ "." ^ (toString m) ^ ")"
  
let rec replace a b arbre liste =
	match arbre with
	| Var x -> if List.exists ((fun a b -> a = b) x) liste then Var x else if a <> x then Var x else b
	| CInt n -> ofInt n
	| Abs (y, m) -> if y <> a then Abs(y, replace a b m (y::liste) ) else Abs (y, m)
	| App (a1, a2) -> App(replace a b a1 liste, replace a b a2 liste)


  
let rec unify2 arbre = 
	match arbre with
	| Var x -> Var x
	| Abs (x, m) -> let v = !index in let () = index := !index + 1 in Abs ((getGrec v), replace x (Var (getGrec v)) (unify2 m) [])
	| App (m, n) -> App(unify2 m, unify2 n)
	| _ -> Var "erreur"
let unify arbre = 
    let () = index := 0 in unify2 arbre
let rec abstraction (l:string list) (m:termWithInfo) (inf:expInfo) :termWithInfo= 
  match l with 
  |[] -> m
  |x::suite -> AbsExt((x, abstraction suite m inf),inf)

let rec compute arbre=match arbre with
			App(Var op,m)->doCalcUnaryOp (Var op) (compute m)
			|App(App((Var op),m),n)->doCalcBinaryOp (Var op) (compute m) (compute n)
			|App(App(App(Var op,m),n),p) as t when op="ifElse"-> (try (compute(doCalcTripletOp (Var op) (compute m) n p)) with StopRec->t )
			|App(App(App(Var op,m),n),p) ->doCalcTripletOp (Var op) (compute m) (compute n) (compute p)
			|_ as t->t
			
  let  reduce arbre = 
 let rec findNormalF arbre =
	match arbre with
	| Var x -> Var x
	| CInt x -> ofInt x
	| Abs (x, m) -> Abs (x, findNormalF m)
	| App (Abs(x, m), n) -> (*let () = print_string (toString (arbre)) in let () = print_newline() in *)let rm = (replace x n m []) in rm
	| App (Var x, n) -> (App(Var x, findNormalF n))
	| App (CInt x, n) -> (App(ofInt x, findNormalF n))
	| App(App(App(Var op,m),n),p) as t when op="ifElse"-> (try (findNormalF(doCalcTripletOp (Var op) (compute (findNormalF m)) n p)) with StopRec->t )
	| App (m, n) ->let rm = findNormalF m in if rm = m then 
			App(m, findNormalF n)  else findNormalF (App(rm, n))
		in let normalForm= findNormalF arbre
		in  compute normalForm


(*let isNormal arbre = arbre = reduce arbre
let rec reduceTerm arbre = 
	let a = ref arbre in 
		while not(isNormal !a) do
			a := reduce !a	
		done; !a
*)

let rec reduceTerm a =  
	let pv = reduce a in if pv = a then a else reduceTerm pv 
	






let rec isAppNumberl a b n = 
	match n with
	| Var x -> if x = b then true else false
	| App(Var x, m) -> if x = a then isAppNumberl  a b m else false
	| _ -> false
let isNumberl n = 
	match n with
	| Abs(x, Abs(y, m)) -> isAppNumberl x y m
	| _ -> false


let rec getAppNumberl n = 
	match n with
	| Abs(a, Abs(b, m)) -> m
	| _ -> Var ""

let rec getNumberl n = 
	match n with
	| Var x -> 0
	| App(a, b) -> 1 + getNumberl b
	| _ -> 0



let cons a b = App(App(Var "cons",a),b)
let print_lreduce term = 
	let t = (reduceTerm term) in
	if isNumberl t 
	then string_of_int (getNumberl (getAppNumberl t))
	else (toString  t)

let print_lmb term = 
	if isNumberl (((term))) 
	then string_of_int (getNumberl (getAppNumberl(( (term)))))
	else (toString  (((term))))