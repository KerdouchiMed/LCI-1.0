(*Computer Science Department, UMBB, 2015*)



open Global;;
open UnificationAlgorithm;;

(*DOC:stringListTostring|string list->string|Fonction permettant de généré une
chaine de caractère résultat de la concaténation de ceux qui sont dans 
l'ensemble set*)
let rec stringListTostring set=
	match set with
	[]->""
	|e::s-> "[" ^ e ^ "]" ^ stringListTostring s;;  

(*DOC:typeToString|unifTypeDef->string|Fonction qui permet de transformer le
type d'un lambda terme d'une forme adapter au traitement <unfiTypeDef> à une
chaine de caractères adapter à l'affichage et le débogage*)
let rec typeToString (t:unifTypeDef)=
	match t with
	TypeVar x->x
	|F(t1,t2)->"(" ^(typeToString t1)^ " -> " ^(typeToString t2)^ ")";;

(*DOC:envToString|(string*unifTypeDef) list->string|Fonction qui permet de
transformer un environnement de typage d'une forme adaptée au traitement 
<(string*unifTypeDef) list> à une chaine de caractères adaptée à 
l'affichage et le débogage*)	
let rec envToString (env:(string*unifTypeDef) list) :string=
	match env with
	[]->""
	|x::l->match x with (var,t)->"("^var^":"^(typeToString t)^")"^" "^(envToString l);;

(*DOC:termToString|term->string|Fonction qui permet de transformer un lambda 
terme d'une forme adaptée au traitement <term> à une chaine de caractères 
adaptée à l'affichage et le débogage*) 
let rec  termToString (t:term) :string=
	match t with
	CInt x -> string_of_int x
	|Var x -> x
	|Abs(x,t)->"("^ "\\"^ x ^ "." ^(termToString t)^")"
	|App(t1,t2)->"("^ (termToString t1) ^ " " ^ (termToString t2)^")";;

(*DOC:equationSetToStr|unifEqu list->string|Fonction qui permet de transformer
un ensemble d'equations d'une forme adaptée au traitement <unifEqu list> à une
chaine de caractères adaptée à l'affichage et le débogage*)
let rec equationSetToStr (p:unifEqu list) :string=
	match p with
	[]->""
	|Eq(t1,t2)::p1->"["^(typeToString t1)^"="^(typeToString t2)^"]"^(equationSetToStr p1) ;;

(*DOC:genTypeName|int->string|Fonction qui prend en entrée un entier, et
retourne un nom utilisé pour nommer les types des variables*)	
let genTypeName n = 
	match n with
	|0->"''a"	|1->"''b"	|2->"''c"	|3->"''d"	|4->"''e"	|5->"''f"	
	|6->"''g"	|7->"''h" |8->"''i" |9->"''j" |10->"''k"|11->"''l"
	|12->"''m"|13->"''n"|14->"''o"|15->"''p"|16->"''q"|17->"''r"	
	|18->"''s"|19->"''t"|20->"''u"|21->"''v"|22->"''w"|23->"''x"	
	|24->"''y"|25->"''z"|_ as x->("''a"^ string_of_int x) ;;


(*DOC:lookup|(string*unifTypeDef) list-> string->unifTypeDef|Fonction qui 
prend entrée un environnement de typage, un nom de variable, et recherche
le type de la variable dans l'environnement,elle le retourne s'il existe,
sinon elle déclanche une execption de type <Failure of string>*)
let rec lookup env x= 
	match env with
	[]->raise (Failure ("Can't find the type of the unbound variable "^x^" in the environment"))
	|(name,t)::l-> if name=x then t else lookup l x ;;
 
 let rec lookupTest env x=
	match env with
	[] -> false
	|(n,t)::l -> if n=x then true else lookupTest l x 

let i =ref 0
let renameType t:unifTypeDef = let ()= i:= !i+1 in let rec renameType t = 
	match t with
	TypeVar x when ((isInternalVar x) || (isUserVar x)) -> TypeVar (x^string_of_int !i)
	|F(a,b)				-> F(renameType a,renameType b)
	|TypeVar x			-> TypeVar x
	in renameType t;;
	
(*DOC:genESetString|term->(string*unifTypeDef) list->unifTypeDef->string list
|Fonction permetant de générer un ensemble(de type string list) d'equations 
obtenu en appliquant l'algorithme de Hindley-Milner sur le terme en entrés
avec comme type de départ <termType>, cette fonction est utiisée selement
pour le débogage *)
(*let genESetString term (env:(string*unifTypeDef) list) termType = let n=ref 0 in
	let rec genESetString term (env:(string*unifTypeDef) list) termType  = 
	match term with
	Var(x)->[ termType  ^ "=" ^ unifTypeDefToString (lookup env x) ]
	|Abs(x,term1)->let a=(genTypeName !n) in let b=genTypeName (!n+1) in n:=!n+2;
						[ a ^ "->" ^ b ^ "=" ^ termType ] @ (genESetString term1 (env@[(x,TypeVar a)]) b)
	|App(term1,term2)->let a=(genTypeName !n) in n:=!n+1;(genESetString term1 env (a ^ "->" ^ termType))@ (genESetString term2 env a)
			in  genESetString term env termType ;;
			*)
(*DOC:genESet|term->(string*unifTypeDef) list->unifTypeDef->unifEqu list
|Fonction permettant de générer un ensemble(de type unifEqu list) 
d'equations obtenu en appliquant l'algorithme de Hindley-Milner 
sur le terme en entrés avec comme type de départ <termType>, 
cette fonction represente la première phase du méchanisme du
typage, la sortie de cette fonction est utilisé comme une
entrée de la celle qui retrouve l'unificateur principale*)
(*let  genEqSet term (env:(string*unifTypeDef) list) termType=  let n=ref 0 in  let _ = i:=0 in
	let rec genEqSet term (env:(string*unifTypeDef) list) termType  = 
	match term with
	CInt x  -> let t = renameType (Global.F(Global.F(Global.TypeVar "''z",Global.TypeVar "''z"),
						Global.F(Global.TypeVar "''z",Global.TypeVar "''z"))) in [Eq(termType,t)]
	|Var(x)-> let t=if(lookupTest env x) then (lookup env x) else renameType (lookup !Global.funType x) in [Eq(termType,t)] 
	|Abs(x,term1)->let a=(genTypeName !n) in let b=genTypeName (!n+1) in n:=!n+2;
						[ Eq(F(TypeVar a,TypeVar b),termType) ] @ (genEqSet term1 (env@[(x,TypeVar a)]) (TypeVar b))
	|App(term1,term2)->let a=(genTypeName !n) in n:=!n+1; (genEqSet term1 env (F(TypeVar a,termType)) )@ (genEqSet term2 env (TypeVar a) )
		in  genEqSet term env termType ;;*)
		
(*DOC:genESet|term->(string*unifTypeDef) list->unifTypeDef->unifEqu list
|Fonction permettant de générer un ensemble(de type unifEqu list) 
d'equations obtenu en appliquant l'algorithme de Hindley-Milner 
sur le terme en entrés avec comme type de départ <termType>, 
cette fonction represente la première phase du méchanisme du
typage, la sortie de cette fonction est utilisé comme une
entrée de la celle qui retrouve l'unificateur principale*)
let churchIntType=Global.F(Global.F(Global.TypeVar "'a",Global.TypeVar "'a"),Global.F(Global.TypeVar "'a",Global.TypeVar "'a"))
let  genEqSet term (env:(string*unifTypeDef) list) termType=  let n=ref 0 in  let () = i:=0 in
	let rec genEqSet term (env:(string*unifTypeDef) list) termType  = 
	match term with
	CIntExt (x,inf)  ->  let t = renameType (churchIntType) in [EqExt(termType,attachTypeInfo t inf)]
	|VarExt(x,inf)->   let t=if(lookupTest env x) then  (lookup env x) else renameType (lookup !Global.funType x) in [EqExt(termType,attachTypeInfo t inf)] 
	|AbsExt((x,term1),inf)-> let a=(genTypeName !n) in let b=genTypeName (!n+1) in n:=!n+2;
						[ EqExt((FExt((TypeVarExt (a,inf),TypeVarExt (b,getExpInfo term1)),inf)),termType) ] 
						@ ( genEqSet term1 (env@[(x,TypeVar a)]) (TypeVarExt (b,getExpInfo term1)) )
	|AppExt((term1,term2),inf)->  let a=(genTypeName !n) in n:=!n+1; (genEqSet term1 env (FExt((TypeVarExt (a,getExpInfo term2),termType),inf)) )@ (genEqSet term2 env (TypeVarExt (a,getExpInfo term2)) )
		in  genEqSet term env termType ;;		
 
(*DOC:substituteVar|term->string->string->term|Fonction qui prend un terme t,un
identificateur de variable x et un autre identificateur y et substitue toutes
les occurrences libres de x par y dans le terme t elle est utilisée pour 
implementer l'alpha conversion*)
let rec substituteVar (t:termWithInfo) (x:string) (y:string) :termWithInfo=
	match t with 
	VarExt (z,inf) ->if (z=x)then (VarExt (y,inf)) else (VarExt (z,inf))
	|CIntExt(z,inf) -> CIntExt(z,inf)
	|AbsExt((z,t),inf)->if(z=x) then AbsExt((z,t),inf) else AbsExt((z,(substituteVar t x y)),inf)
	|AppExt((t1,t2),inf)->AppExt((substituteVar t1 x y,substituteVar t2 x y),inf);;

(*DOC:genVarName|int->string|Fonction genere un nom de variable dépendant de 
l'entier n elle est utilisée par la fonction qui fait le renomage de toutes 
les variables liées d'un terme*)	
let genVarName (n:int) :string= "_x"^ string_of_int n;;

(*DOC:renameBoundVar|term->term|Fonction qui fait le renomage de toutes les 
variables liées d'un term, cette focntion est appliquée à un lambda term 
avant d'appliqué l'algorithme de Hindley-Milner car elle évite le cas où
deux ou plus de variables liées dans un terme aient le meme nom ce qui 
pose problème*)
let renameBoundVar (t:termWithInfo) :termWithInfo=let n=ref 0 in let rec renameBoundVar t=
 match t with
 |AbsExt((x,t),inf)->let newName=(genVarName !n) in n:=!n+1; AbsExt((newName,renameBoundVar (substituteVar t x newName)),inf)
 |AppExt((t1,t2),inf)->AppExt((renameBoundVar t1,renameBoundVar t2),inf)
 |_ as v-> v
		in renameBoundVar t;;
 
(*DOC:insertIfNotExist|'a list -> 'a -> 'a list|Fonction qui prend en argument
une liste et un element,elle insere l'element à la fin de la liste s'il 
n'existe pas*)
let rec insertIfNotExist (l:'a list) elmnt :'a list=
	match l with
	[]->[elmnt]
	|x::l1->if (elmnt=x) then l else x::insertIfNotExist l1 elmnt;;

(*DOC:fusionListNoRepet|'a list -> 'a list -> 'a list|Fonction qui prend en
argument deux listes et fusionne ces listes, mais de sorte que dans la 
liste résultante, on aura une seul occurrence de chaque élément*)
let rec fusionListNoRepet list1 list2=
	match list1 with
	[]->list2
	|x::l1->insertIfNotExist (fusionListNoRepet l1 list2) x ;;
	
(*DOC:extractFromArrowForm|unifTypeDef->unifTypeDef list|Fonction qui permet
d'extraire l'ensemble des types élémentaires utilisés par un type composé,
par exemple le type (int->bool->int->float) donnera l'ensemble 
[int;bool;float]*)
let extractFromArrowForm (t:unifTypeDef) :unifTypeDef list=let typeList=ref [] in
	let rec extractFromArrowForm t=
		match t with
		(TypeVar x) as v-> (let _=typeList:=(insertIfNotExist (!typeList) v) in !typeList)
		|F(t1,t2)-> (let _=typeList:=extractFromArrowForm t1;typeList:=extractFromArrowForm t2 in !typeList)  
			in extractFromArrowForm t;;
			
(*DOC:extractTypesFromEnv|(string*unifTypeDef) list->unifTypeDef list|Fonction
qui permet d'extraire l'ensemble des types élémentaires utilisés par un
environnement de typage, par exemple [x:int->int;z:bool] donnera
l'ensemble [int;bool], cette fonction est nécessaire lors de 
l'execution de la phase d'unification : elle est utilisée 
pour généré l'ensemble des types constants que la régle
de l'orientation se serve pour différencier les 
variables de types des constantes et donc 
orionter les equations convenablement*)
let rec extractTypesFromEnv (env:(string*unifTypeDef) list) :unifTypeDef list=
	match env with
	[]->[]
	|(x,t)::l->	fusionListNoRepet (extractFromArrowForm t) (extractTypesFromEnv l)
	;;
		
(*DOC:giveMeTheType|term->(string*unifTypeDef) list->unifTypeDef|Fonction qui
retourne le type d'un lambda terme s'il existe si non elle emit une exception
<Failure "canNotBeTyped">, elle est le fruit de tous ce qui est fait dans les
deux modules inferenceMechanism et UnificationAlgorithm*)
let typed = ref false 
let giveMeTheType (t:termWithInfo) (env:(string*unifTypeDef) list) :unifTypeDefWithInfo=
(* try( *)	let _ = typed := false in
		let inputTerm=t in
		let alphaConvertedTerm=renameBoundVar inputTerm in
		let unifProblem= ref (genEqSet alphaConvertedTerm (env) (TypeVarExt ("''T",getExpInfo t))) in
		let _=(print_string ("\n	-->Ensemble d'equations initiale : "^(equationSetToStr (discardEqSetInfo !unifProblem)));print_newline ();flush stdout) in
		let unifierState = (mguFindAndCheck unifProblem ) in
		let _=(print_string ("\n	-->Ensemble d'equations résolu(si possible) : "^(equationSetToStr (discardEqSetInfo !unifProblem)));print_newline ();flush stdout) in
		if(unifierState) then  let _ = typed := true in  (renameTypeVars(getVarVal !unifProblem (TypeVarExt ("''T",getExpInfo t))))
			else raise (Failure "canNotBeTyped")
(* 	)with *)
(* 		TypeNotFoundInEnv t->raise (Failure "canNotBeTyped");; *)

(*DOC:giveMeTheType|term->(string*unifTypeDef) list->unifTypeDef|Fonction qui
retrouve et affiche le type d'un lambda terme s'il existe si non elle affiche
un echec, elle est le fruit de tous ce qui est fait dans les deux modules
inferenceMechanism et UnificationAlgorithm*)
(*let giveMeTheTypeDebug term env= try
	(
		let inputTerm=term in ( print_string ("	-->Term : "^(termToString inputTerm));print_newline ()
		;print_string ("	-->Environnement de typage : "^(envToString env));print_newline ();
		let constTypes=(extractTypesFromEnv env) in 
		let alphaConvertedTerm=renameBoundVar inputTerm in
		let _= print_string ("	-->Alpha Converted Term : "^(termToString alphaConvertedTerm));print_newline () in
		let unifProblem= ref (genEqSet alphaConvertedTerm (env) (TypeVar "''T")) in
		let _=(print_string ("	-->Ensemble d'equations initiale : "^(equationSetToStr !unifProblem));print_newline ()) in
		let unifierState = (mguFindAndCheck unifProblem constTypes) in
		let _=(print_string ("	-->Ensemble d'equations résolu(si possible) : "^(equationSetToStr !unifProblem));print_newline ()) in
		if(unifierState) then (
			let foundType=(getVarVal !unifProblem (TypeVar "''T")) in
			print_string ("	-->Type : "^(typeToString (foundType)));print_newline () )
			else (
				print_string ("	-->Type : This term doesn't have a type in the given environment !");print_newline ())
				;print_string "Fin analyse";print_newline () );
		print_string "	Inserez un lambda terme et appuyer sur la touche entrer : ";
		print_newline ()
	)
	with 
		TypeNotFoundInEnv t->(print_string ("	-->Type :This term doesn't have a type in the given environment ! : "^t)
									;print_newline ());;
	*)								
(*DOC:normalizeExpression|term->term|Fonction qui permet de transformer une
expression obtenu depuis le parser à une expression totalement compatible
avec le mecanisme du typage*)
exception CanNotBeNormalized;;
let rec normalizeExpression exp=
	match exp with
	Var x->Var x
	|CInt x->CInt (x)
	|Abs(x,y)->Abs(x,normalizeExpression y)
	|App(x,y)->App(normalizeExpression x,normalizeExpression y)

	
let rec insertTypSansRep (name,typ) fnTyp =
	match fnTyp with
	|[] 		-> [(name,typ)]
	|(nam,ty)::l 	-> if nam=name then (name,typ)::l else (nam,ty)::(insertTypSansRep (name,typ) l)

let rec getIntTyp typ =
match typ with 
TypeVar x -> TypeVar x
|F(x,y)   -> match (x,y) with
	      (TypeVar a,TypeVar b) -> F(TypeVar a,TypeVar b)
	      |(TypeVar a,_) -> F(TypeVar a,getIntTyp y)
	      |(_,TypeVar y) -> F(getIntTyp (x),TypeVar y)
	      |(F(a,b),F(c,d)) -> match ((a,b),(c,d)) with
				  ((TypeVar a,TypeVar b),(TypeVar c,TypeVar d)) when ((a=b) && (b=c) && (c=d))  -> TypeVar "int"
				  |_  -> F(getIntTyp (F(a,b)),getIntTyp (F(c,d)))
				  
				  
let main exp env = 
 try (
	typeToString ( (discardTypeInfo(giveMeTheType exp env)))
     )
     with 
     Failure s -> s 
	      