type pos=
	LigneCar of (int*int)

type expPos=
	Position of pos*pos
type expInfo=
{
	localisation : expPos;
	
}

type term=
	|Var of string 
	|Abs of string * term
	|App of term*term 
	|CInt of int
type termWithInfo=
	|VarExt of string * expInfo
	|AbsExt of (string * termWithInfo)*expInfo
	|AppExt of (termWithInfo*termWithInfo) * expInfo
	|CIntExt of int * expInfo

type unifTypeDef=
	TypeVar of string
	|F of unifTypeDef*unifTypeDef;;

type unifTypeDefWithInfo=
	TypeVarExt of string*expInfo
	|FExt of (unifTypeDefWithInfo*unifTypeDefWithInfo)*expInfo;;	
	
type unifEqu=
	Eq of unifTypeDef*unifTypeDef;;

type unifEquWithInfo=
	EqExt of unifTypeDefWithInfo*unifTypeDefWithInfo;;	
	
type parserOut =
	Term of term
	|Type of unifTypeDef
	|Unit of unit
	|StringList of  (string list);;

	
let rec abstractVars (varList:string list) term=
	match varList with
	[]->term
	|x::l->Abs(x,abstractVars l term);;

let rec discardInfo (t:termWithInfo) :term= 
	match t with
	VarExt(e,_)-> Var(e) 
	|AbsExt((v,t),_) -> Abs(v,discardInfo t)
	|AppExt((t1,t2),_) -> App(discardInfo t1,discardInfo t2)
	|CIntExt(i,_) -> CInt(i)
	
let rec attachInfo (t:term) (inf:expInfo) :termWithInfo= 
	match t with
	Var(e) -> VarExt(e,inf)
	|Abs(v,t) -> AbsExt((v,attachInfo t inf),inf) 
	|App(t1,t2) -> AppExt((attachInfo t1 inf,attachInfo t2 inf),inf) 
	|CInt(i) -> CIntExt(i,inf)

let rec discardTypeInfo (t:unifTypeDefWithInfo) :unifTypeDef= 
	match t with
	TypeVarExt(v,_)->TypeVar(v) 
	|FExt((t1,t2),_)->F(discardTypeInfo t1,discardTypeInfo t2)	
	
	
let rec attachTypeInfo (t:unifTypeDef) (inf:expInfo) :unifTypeDefWithInfo= 
	match t with
	TypeVar(v) -> TypeVarExt(v,inf)
	|F(t1,t2) -> FExt((attachTypeInfo t1 inf,attachTypeInfo t2 inf),inf)	

let rec discardEqSetInfo eqSet =
	match eqSet with
	[]->[]
	|EqExt(t1,t2)::l->Eq(discardTypeInfo t1,discardTypeInfo t2)::discardEqSetInfo l
	
let getExpInfo t=
	match t with
	CIntExt (_,inf) -> inf
	|VarExt (_,inf) -> inf
	|AbsExt((_,_),inf) -> inf
	|AppExt((_,_),inf) -> inf

let getTypeInfo t=
	match t with
	TypeVarExt(_,inf) -> inf
	|FExt((_,_),inf) -> inf

let printInf inf=
	let (Position(LigneCar(l1,c1),LigneCar(l2,c2)))=inf.localisation in
    if(l1 = l2) then ("ligne "^(string_of_int l1)^",characters "^(string_of_int c1)^"-"^(string_of_int c2)^": ") 
    else ("ligne "^(string_of_int l1)^",character "^(string_of_int c1)^"- ligne "^(string_of_int l2)^",character "^(string_of_int c2)^": ")
	
let currentBuffer=ref ""	
let envc:(string*unifTypeDef)list ref = ref []
let funType:(string*unifTypeDef)list ref = ref []
let functions = ref []
let protectedIdents = ref []

(*Combinators Definitions*) 
let ss =  (Abs ("x", Abs("y", Abs("z", App(App(Var "x", Var "z"), App(Var "y", Var "z"))))))
let bb =  (Abs ("x", Abs("y", Abs("z", App(Var "x", App(Var "y", Var "z"))))))
let cc =  (Abs ("x", Abs("y", Abs("z", App(App(Var "x", Var "z"), Var "y")))))
let ii =  (Abs ("x", Var "x"))
let kk =  (Abs ("x", Abs ("y", Var "x")))

(*Combinators types*)
let typeS= 	F(F(TypeVar "'e",F(TypeVar "'g",TypeVar "'f")),F(F(TypeVar "'e",TypeVar "'g"),F(TypeVar "'e",TypeVar "'f")))	(*(('e -> ('g -> 'f)) -> (('e -> 'g) -> ('e -> 'f)))					*)				
let typeK=	F(TypeVar "'a",F(TypeVar "'c",TypeVar "'a")) (*('a -> ('c -> 'a))*)
let typeI= 	F(TypeVar "'a",TypeVar "'a") (*("'a -> "'a)*)
let typeB= 	F(F(TypeVar "'g",TypeVar "'f"),F(F(TypeVar "'e",TypeVar "'g"),F(TypeVar "'e",TypeVar "'f")))(*(('g -> 'f) -> (('e -> 'g) -> ('e -> 'f)))*)
let typeC= 	F(F(TypeVar "'e",F(TypeVar "'c",TypeVar "'f")),F(TypeVar "'c",F(TypeVar "'e",TypeVar "'f"))) (*(('e -> ('c -> 'f)) -> ('c -> ('e -> 'f)))*)
(*Logical operators types*)
(*let typeOr= F(TypeVar "bool",F(TypeVar "bool",TypeVar "bool"))
let typeAnd=F(TypeVar "bool",F(TypeVar "bool",TypeVar "bool"))
let typeNot=F(TypeVar "bool",TypeVar "bool")
let typeTestEqual=F(TypeVar "'a",F(TypeVar "'b",TypeVar "bool"))*)

(*Le combinateur Y pour les fonctions récursives*)
let fix=App(Abs("x",Abs("f",App(Var "f",App(App(Var "x",Var "x"),Var "f")))),Abs("x",Abs("f",App(Var "f",App(App(Var "x",Var "x"),Var "f")))));;
let typeFix=F(F(TypeVar "'a",TypeVar "'a"),TypeVar "'a");;

(*fonctions and types *)
let succ = (Abs("n",Abs("f",Abs("x" ,App(Var "f",App(App(Var "n",Var "f"),Var "x")))))) 
let pred = (Abs("n",Abs("f",Abs("x" ,App(App(App(Var "n" , Abs("g",Abs("h",App(Var "h",App(Var"g",Var"f"))))),Abs("u",Var"x")),Abs("u",Var"u")))))) 
	let unType = (F((F(F(TypeVar "'a",TypeVar "'a"),F(TypeVar "'a",TypeVar "'a")),(F(F(TypeVar "'a",TypeVar "'a"),F(TypeVar "'a",TypeVar "'a"))))));;

let add = (Abs("m",Abs("n",Abs("f",Abs("x" ,App(App(Var "m",Var "f"),App(App(Var "n",Var "f"),Var "x"))))))) 
let sub = (Abs("m",Abs("n",App(App(Var "n",Var"pred"),Var"m")))) 
let mul = (Abs("m",Abs("n",Abs("f",App(Var "m",App(Var "n",Var "f")))))) 
	let binType = (F((F(F(TypeVar "'a",TypeVar "'a"),F(TypeVar "'a",TypeVar "'a"))),
		F((F(F(TypeVar "'a",TypeVar "'a"),F(TypeVar "'a",TypeVar "'a"))),(F(F(TypeVar "'a",TypeVar "'a"),F(TypeVar "'a",TypeVar "'a"))))));;

let ltrue = (Abs("a",Abs("b",Var"a"))) 
let lfalse =  (Abs("a",Abs("b",Var"b"))) 
	let boolType = (F(TypeVar "'a",F(TypeVar "'a",TypeVar "'a")))

let iszero = (Abs("n",App(App(Var"n",Abs("x",Abs("a",Abs("b",Var"b")))),Abs("a",Abs("b",Var"a"))))) 
	let iszeroType = (F(F(F(TypeVar "'a",TypeVar "'a"),F(TypeVar "'a",TypeVar "'a")),(F(TypeVar "'b",(F(TypeVar "'b",TypeVar "'b"))))));;



(*Remplissage de l'environnement par les types connus*)
(*(funType:=("or", typeOr)::!funType);
(funType:=("and", typeAnd)::!funType);
(funType:=("neg", typeNot)::!funType);*)
(funType:=("fix", typeFix)::!funType);
(funType:=("mul", binType)::!funType);
(funType:=("add", binType)::!funType);
(funType:=("sub", binType)::!funType);
(funType:=("succ", unType)::!funType);
(funType:=("pred", unType)::!funType);
(funType:=("iszero", iszeroType)::!funType);
(funType:=("ltrue", boolType)::!funType);
(funType:=("lfalse", boolType)::!funType);
	(*Par les types des combinateurs*)
(funType:=("S", typeS)::!funType);
(funType:=("K", typeK)::!funType);
(funType:=("I", typeI)::!funType);
(funType:=("B", typeB)::!funType);
(funType:=("C", typeC)::!funType);


(*Remplissage de l'environnement des fonctions déclarées par les fonctions connus*)
(functions:=("fix",fix)::!functions);
(functions:=("pred",pred)::!functions);
(functions:=("succ",succ)::!functions);
(functions:=("mul",mul)::!functions);
(functions:=("add",add)::!functions);
(functions:=("sub",sub)::!functions);
(functions:=("lfalse",lfalse)::!functions);
(functions:=("ltrue",ltrue)::!functions);
(functions:=("iszero",iszero)::!functions);
	(*Par les combinateurs*)
(functions:=("I",ii)::!functions);
(functions:=("S",ss)::!functions);
(functions:=("K",kk)::!functions);
(functions:=("B",bb)::!functions);
(functions:=("C",cc)::!functions);

(* Protection des identificateurs internes *)
protectedIdents:=
[
"S"
;"K"
;"I"
;"B"
;"C"
;"fix"
;"mul"
;"add"
;"sub"
;"succ"
;"pred"
;"iszero"
;"ltrue"
;"lfalse"
]