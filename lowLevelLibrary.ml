open Global

let aritmeticIntOpType=F(TypeVar "int",F(TypeVar "int",TypeVar "int"))
let aritmeticRealOpType=F(TypeVar "real",F(TypeVar "real",TypeVar "real"))
let boolOpType=F(TypeVar "bool",F(TypeVar "bool",TypeVar "bool"))
let notOpType=F(TypeVar "bool",TypeVar "bool")
let cmpOpType=F(TypeVar "'a",F(TypeVar "'a",TypeVar "bool"))
let ifElseType=F(TypeVar "bool",F(TypeVar "'a",F(TypeVar "'a",TypeVar "'a")))

let _ =(funType:=("-1", TypeVar "int")::!funType)
let _ =(funType:=("-1.", TypeVar "real")::!funType)
(* Operateur plus *)
let integerPlus=(Var "+")
	let _ =(funType:=("+", aritmeticIntOpType)::!funType)
let realPlus=(Var "+.")
	let _ =(funType:=("+.", aritmeticRealOpType)::!funType)

(* Operateur moins *)
let integerMinus=(Var "-")
	let _ =(funType:=("-", aritmeticIntOpType)::!funType)
let realMinus=(Var "-.")
	let _ =(funType:=("-.", aritmeticRealOpType)::!funType)

(* Operateur de multiplication *)
let integerMult=(Var "*")
	let _ =(funType:=("*", aritmeticIntOpType)::!funType)
let realMult=(Var "*.")
	let _ =(funType:=("*.", aritmeticRealOpType)::!funType)

(* Operateur de division *)
let integerDiv=(Var "/")
	let _ =(funType:=("/", aritmeticIntOpType)::!funType)
let realDiv=(Var "/.")
	let _ =(funType:=("/.", aritmeticRealOpType)::!funType)

(* Operateur Or *)
let boolOr=(Var "||")
	let _ =(funType:=("||", boolOpType)::!funType)

(* Operateur And *)
let boolAnd=(Var "&&")
	let _ =(funType:=("&&", boolOpType)::!funType)

(* Operateur not *)
let boolNot=(Var "not")
	let _ =(funType:=("not", notOpType)::!funType)

(* Operateur d'égalité *)
let equal=(Var "==")
	let _ =(funType:=("==", cmpOpType)::!funType)

(* Operateur supériorité *)
let higherThan=(Var ">")
	let _ =(funType:=(">", cmpOpType)::!funType)

(* Operateur infériorité *)
let lessThan=(Var "<")
	let _ =(funType:=("<", cmpOpType)::!funType)

(* l'instruction if ... then ... else ...	*)
let ifElse=(Var "ifElse")
	let _ =(funType:=("ifElse", ifElseType)::!funType)
	
			(* fonctions mathématiques *)
(* racine carrée *)
let sqrtFun=(Var "sqrt")
	let _ =(funType:=("sqrt", F(TypeVar "real",TypeVar "real"))::!funType)

	
	
exception OperatorExpected
exception ArgError
exception StopRec
let isInt arg=try int_of_string arg with Failure t->raise ArgError 
let isReal arg=try float_of_string arg with Failure t->raise ArgError
let isBool arg= if (arg="true") then true else if (arg="false") then false else raise ArgError
let boolToLambdaBool b=if b=true then Abs("x",Abs("y",Var "x")) else if b=false then Abs("x",Abs("y",Var "y")) else raise ArgError

let doCalcTripletOp op arg1 arg2 arg3= 
try 
(
	match (arg1,arg2,arg3) with
	(x,y,z) when op=ifElse->( match x with (Var v)->(try(if(isBool v) then y else z) with ArgError->raise StopRec)
													 |_->raise StopRec )
	|_->App(App(App(op,arg1),arg2),arg3)
)
with 
ArgError->App(App(App(op,arg1),arg2),arg3)

let doCalcBinaryOp op arg1 arg2= 
 try 
 (
	match (arg1,arg2) with
	(Var x,Var y) when op=integerPlus->Var (string_of_int((isInt x) + (isInt y)))
	|(Var x,Var y) when op=realPlus->Var (string_of_float((isReal x) +. (isReal y)))
	|(Var x,Var y) when op=integerMinus->Var (string_of_int((isInt x) - (isInt y)))
	|(Var x,Var y) when op=realMinus->Var (string_of_float((isReal x) -. (isReal y)))
	|(Var x,Var y) when op=integerMult->Var (string_of_int((isInt x) * (isInt y)))
	|(Var x,Var y) when op=realMult->Var (string_of_float((isReal x) *. (isReal y)))
	|(Var x,Var y) when op=integerDiv->Var (string_of_int((isInt x) / (isInt y)))
	|(Var x,Var y) when op=realDiv->Var (string_of_float((isReal x) /. (isReal y)))
	|(Var x,Var y) when op=boolOr->Var (string_of_bool((isBool x) || (isBool y)))
	|(Var x,Var y) when op=boolAnd->Var (string_of_bool((isBool x) && (isBool y)))
	|(Var x,Var y) when op=equal->(try (Var (string_of_bool(isInt x = isInt y)) )
												with ArgError -> try (Var (string_of_bool(isReal x = isReal y)) )
																			with ArgError-> Var (string_of_bool(isBool x = isBool y)))
	|(Var x,Var y) when op=higherThan->(try Var (string_of_bool((isInt x) > (isInt y))) with ArgError-> Var (string_of_bool((isReal x) > (isReal y))))
	|(Var x,Var y) when op=lessThan->(try Var (string_of_bool((isInt x) < (isInt y))) with ArgError-> Var (string_of_bool((isReal x) < (isReal y))))
	|_->App(App(op,arg1),arg2)
 )
 with 
 ArgError->App(App(op,arg1),arg2)
 
 let doCalcUnaryOp op arg=
 try 
 (
	 match arg with
	 Var x when op=boolNot->Var (string_of_bool(not(isBool x)))
	 |Var x when op=sqrtFun->Var (string_of_float(sqrt(isReal x)))
	 |_->App(op,arg)
 )
 with 
 ArgError->App(op,arg)
 