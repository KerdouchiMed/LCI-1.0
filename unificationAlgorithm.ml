(*Computer Science Department, UMBB, 2015*)



open Global

exception Failure of string ;;

type genTypeFunMode=Internal | User | Const;;
(*DOC:genTypeName|int->string|Fonction qui prend en entrée un entier, et
retourne un nom utilisé pour nommer les types des variables*)	
let genTypeName n kind= 
	(match kind with
		Internal->"''"
		|User->"'"
		|_->"")^
	match n with
		|0->"a"	|1->"b"	|2->"c"	|3->"d"	|4->"e"	|5->"f"	
		|6->"g"	|7->"h" |8->"i" |9->"j" |10->"k"|11->"l"
		|12->"m"|13->"n"|14->"o"|15->"p"|16->"q"|17->"r"	
		|18->"s"|19->"t"|20->"u"|21->"v"|22->"w"|23->"x"	
		|24->"y"|25->"z"|_ as x->("a"^ string_of_int x) ;;

(*DOC:typeToString|unifTypeDef->string|Fonction qui permet de transformer le
type d'un lambda terme d'une forme adapter au traitement <unfiTypeDef> à une
chaine de caractères adapter à l'affichage et le débogage*)
let rec typeToString (t:unifTypeDef)=
	match t with
	TypeVar x->x
	|F(t1,t2)->"(" ^(typeToString t1)^ " -> " ^(typeToString t2)^ ")";;
		
(*DOC:equationSetToStr|unifEqu list->string|Fonction qui permet de transformer
un ensemble d'equations d'une forme adaptée au traitement <unifEqu list> à une
chaine de caractères adaptée à l'affichage et le débogage*)
let rec equationSetToStr (p:unifEqu list) :string=
	match p with
	[]->""
	|Eq(t1,t2)::p1->"["^(typeToString t1)^"="^(typeToString t2)
		
(*DOC:unifTypeDefToString|unifTypeDefWithInfo->string|Fonction qui permet de
transformer un type d'une forme adaptée au traitement 
<unifTypeDefWithInfo> à une chaine de caractères adaptée à 
l'affichage et le débogage*)
let rec unifTypeDefToString (t:unifTypeDefWithInfo) :string=
	match t with
	TypeVarExt (x,_)->x
	|FExt((x,y),_)->"("^ (unifTypeDefToString x)^ "->" ^ (unifTypeDefToString y)  ^")";;

(*DOC:printUnifTypeDef|unifTypeDefWithInfo->unit|Fonction qui permet de
transformer un type d'une forme adaptée au traitement 
<unifTypeDefWithInfo> à une chaine de caractères adaptée à 
l'affichage et le débogage et l'afficher à l'écran*)	
let rec printUnifTypeDef (t:unifTypeDefWithInfo) :unit=
	match t with
	TypeVarExt (x,_)->print_string x
	|FExt((x,y),_)->print_string "F(";printUnifTypeDef x;print_string ",";printUnifTypeDef y;print_string ")";;
	
(*DOC:printProbList|unifEquWithInfo list->unit|Fonction qui permet de 
transformer ensemble d'equations d'une forme adaptée au traitement 
<unifTypeDefWithInfo> à une chaine de caractères adaptée à 
l'affichage et le débogage et l'afficher à l'écran*)
let rec printProbList (p:unifEquWithInfo list) :unit=
	match p with
	[]->print_string ""
	|EqExt(l,r)::p1->print_string "["; printUnifTypeDef l ;print_string "=" ; printUnifTypeDef r ;print_string "]" 
						;printProbList p1;;

(*DOC:deleteRule|unifEquWithInfo list->unifEquWithInfo list|Fonction implemente la règle de la
suppression des equations triviaux : P U {x=x} donnera P *)
let rec deleteRule (p:unifEquWithInfo list) :unifEquWithInfo list=
	match p with
	[]->[]
	|EqExt(l,r)::p1->if ((discardTypeInfo l)=(discardTypeInfo r)) then deleteRule p1  else EqExt(l,r)::(deleteRule p1);;

(*DOC:decomposeRule|unifEquWithInfo list->unifEquWithInfo list|Fonction implemente la règle de
la décomposition : P U {FExt(t1,t2)=FExt(t3,t4)} donnera P U {t1=t3} U {t2=t4}*)
let rec decomposeRule (p:unifEquWithInfo list) :unifEquWithInfo list=
	match p with
	[]->[]
	|EqExt(l,r)::p1->match (l,r) with
					(FExt((x1,y1),_),FExt((x2,y2),_))->decomposeRule (EqExt(x1,x2)::EqExt(y1,y2)::p1)
					|(x,y)->EqExt(x,y)::decomposeRule p1
					;;

(*DOC:exists|'a list->bool|Fonction qui test si x existe dans une liste l,
retourne true s'il existe, si non false, elle est utiliser par la règle de
l'orientation pour tester si un type est une variable ou une constante
connu auparavant*)
let rec exists (l:'a list) x=
	match l with
	[]->false
	|y::l1->if(x=y) then true else exists l1 x;;
	
(*DOC:orientRule|unifEquWithInfo list->unifTypeDefWithInfo list->unifEquWithInfo list|Fonction 
implemente la règle de l'orientation : P U {FExt(t1,t2)=x} tel que x
est une variable donnera P U {x=FExt(t1,t2)} et  P U {c=x} tel que x 
est une variable , c une constante(existe dans l'ensemble des 
constantes) donnera P U {x=c} , et P U {c1=c2} genérera une 
exception de type <Failure "distinctTypeEquality"> puisque
c1 et c2 sont deux types dintincts*)
let isInternalVar name=if (String.length name) > 2 then (if(String.sub name 0 2)="''" then true else false)else false
let isUserVar name=if ((String.length name) > 1) && name.[0] = '\'' then true else false
let isComposedType t= match t with FExt(_,_)->true |_-> false 
let isConstVar v= (not(isInternalVar v) && not(isUserVar v))
let rec typeToUserVars (t:unifTypeDefWithInfo)=
	match t with 
	TypeVarExt (x,inf)->if(isInternalVar x) then TypeVarExt (("'_"^(String.sub x 2 ((String.length x)-2) )),inf) else TypeVarExt (x,inf)
	|FExt((t1,t2),inf)->FExt((typeToUserVars t1,typeToUserVars t2),inf);;

let rec orientRule (p:unifEquWithInfo list)  :unifEquWithInfo list=
	match p with
	[]->[]
	|EqExt(l,r)::p1->match (l,r) with
			(_ as t1,(TypeVarExt (iV,inf) as t2)) when (match t1 with TypeVarExt (v,_) when isInternalVar v->false |_->true) 
						&& isInternalVar iV-> (EqExt(t2,t1))::orientRule p1 
			|(TypeVarExt (v,_) as t1,t2) when  isConstVar v && isComposedType t2->EqExt(t2,t1)::orientRule p1 
			|(TypeVarExt (c,_) as t1,(TypeVarExt (uV,_) as t2)) when (isConstVar c) && (isUserVar uV)->EqExt(t2,t1)::orientRule p1 
			|(t1,(TypeVarExt (uV,_) as t2)) when (isComposedType t1) && (isUserVar uV)->EqExt(t2,t1)::orientRule p1 
			|(TypeVarExt (c1,_) ,(TypeVarExt (c2,inf) )) when (isConstVar c1) && (isConstVar c2)
									-> raise (Failure ("Error "^(printInf inf)^"\n		This expression has type "^c2^" but an expression was expected of type "^c1))
			|(t1,t2) ->EqExt(t1,t2)::orientRule p1 	;;

    
			
(*DOC:|unifTypeDefWithInfo->unifTypeDefWithInfo->bool|Fonction qui teste si un type elementaire
x existe dans un type ut, retourne true si oui, si non retourne false, elle est
utilisée par la règle qui teste l'occurence d'une variable dans les deux 
extrimité d'une equation <occurCheck>*)
let rec checkXExistence (ut:unifTypeDefWithInfo) (x:unifTypeDefWithInfo) :bool=
	match ut with
	TypeVarExt (z,_) as v->if(discardTypeInfo v=discardTypeInfo x) then true else false
	|FExt((t1,t2),_)->if (checkXExistence t1 x) then true else (checkXExistence t2 x) ;;

(*DOC:occurCheckRule|unifEquWithInfo list->bool|Fonction implemente la règle de 
vérification de l'echec x=t ou x apparait dans t *)
let rec occurCheckRule (p:unifEquWithInfo list) :bool=
	match p with
	[]->false
	|EqExt(TypeVarExt (x,inf) as t1,(FExt((_,_),_) as t2))::p1->	
				if(checkXExistence t2 t1)  then raise (Failure ("Error "^(printInf inf)^"\n          This expression has type "^(unifTypeDefToString t2)^
									  "\n          but an expression was expected of type "^(unifTypeDefToString t1)^
									  "\n          The type variable "^(unifTypeDefToString t1)^" occurs inside "^(unifTypeDefToString t2))
				) else occurCheckRule p1
	|EqExt(FExt((_,_),_) as t1,((TypeVarExt (x,inf)) as t2))::p1->if(checkXExistence t1 t2) then 
								raise (Failure ("Error "^(printInf inf)^"\n          This expression has type "^(unifTypeDefToString t1)^
									  "\n          but an expression was expected of type "^(unifTypeDefToString t2)^
									  "\n          The type variable "^(unifTypeDefToString t2)^" occurs inside "^(unifTypeDefToString t1))
								    ) else occurCheckRule p1
	|_::p1->occurCheckRule p1 ;;
												

let nbSub=ref 0;;(*Stocke le nombre de substitutions faite par la fonction replaceXbyY*)
(*DOC:replaceXbyY|unifTypeDefWithInfo->unifTypeDefWithInfo->unifTypeDefWithInfo->unifTypeDefWithInfo|Fonction 
qui remplace toutes les occurrences de x par y dans un terme ut et incrémente
la référence nbSub en chaque substitution faite, elle est utilisée par la
fonction <substitute> qui est utilisé par la règle de substitution*)
let rec replaceXbyY (ut:unifTypeDefWithInfo) (x:unifTypeDefWithInfo) (y:unifTypeDefWithInfo) :unifTypeDefWithInfo= 
				match (ut,x) with
				(TypeVarExt (v1,_),TypeVarExt (v2,_)) when v1=v2->let _ = (nbSub:=!nbSub+1) in y
				|(FExt((t1,t2),inf),_)->FExt((replaceXbyY t1 x y,replaceXbyY t2 x y),inf)
				|(x,_)->x
			;;
 
(*DOC:substitute|unifEquWithInfo list->unifTypeDefWithInfo->unifTypeDefWithInfo->unifEquWithInfo list|Fonction 
qui remplace toutes les occurrences de x par y dans un ensemble d'equation p
,elle est utilisée par la règle de substitution*)
let rec substitute (p:unifEquWithInfo list) (x:unifTypeDefWithInfo) (y:unifTypeDefWithInfo) :unifEquWithInfo list= let _ = (nbSub:=0) in 
 (
	 match p with
	 []->[]
	 |EqExt(l,r)::p1->EqExt(replaceXbyY l x y,replaceXbyY r x y)::substitute p1 x y 
 );;

(*DOC:beTheLastElmnt|'a list -> 'a -> 'a list|Fonction qui prend une liste, un
element, et insert l'element à la fin de la liste*)
let beTheLastElmnt p x=p@[x];;

let substituteRuleState=ref false;; (*true veut dire qu'une ou plusieurs substitutions sont appliqées
													false veut dire qu'aucune  n'est appliqée*)													

(*DOC:substituteRule|unifEquWithInfo list->unifEquWithInfo list|Fonction implemente la règle de
la substitution : si pas d'occurCheck et pas d'equations triviaux alors
P U {x=t} donnera [x->t]P U {x=t}, s'il y a occurCheck alors une
exception <Failure "occurCheck"> est déclancher*)
let  substituteRule (p:unifEquWithInfo list) :unifEquWithInfo list=  let _ =substituteRuleState:=false in let rec substituteRule  p nbMetElmnt=(*print_string "hello";*)(
	 let _ =occurCheckRule p in
			match p with
			[]->[]
			|EqExt(l,r)::p1->(if(nbMetElmnt=(List.length p) && !nbSub=0) then p
							else 
								(
									match l with
									(TypeVarExt (x,_)) as t  when ((isInternalVar x)||(isUserVar x))  ->let result = (substitute p1 t r) in
												if(!nbSub>0) then let _=substituteRuleState:=true in
																	substituteRule (deleteRule(beTheLastElmnt result (EqExt(l,r)))) 0
												else 	substituteRule (beTheLastElmnt result (EqExt(l,r))) (nbMetElmnt+1)
									|_->substituteRule  (beTheLastElmnt p1 (EqExt(l,r))) (nbMetElmnt+1)
								)
							) 
		)
		 in substituteRule p 0 ;;
		 
(*la règle de la collision de noms, exemple : FExt(a,b)=G(z,y),cette règle ne sera pas implementer pour le moment
du fait que les types utilise seulement FExt, et pas autres symboles*)

exception EndOfExec of string;;

(*DOC:substitAndTestEnd|unifEquWithInfo list->unifEquWithInfo list|Fonction qui est une 
extention de la règle de la substitution, celle ci permet en plus 
de déclancher une exception <EndOfExec "noSubtitutionDone"> si 
aucune substitution n'est faite et donc arreter la recherche 
de l'unificateur*)
let substitAndTestEnd (p:unifEquWithInfo list) =let result=substituteRule p in 
			if (!substituteRuleState=false) then
				raise  (EndOfExec "noSubtitutionDone")
			else
				result;;

(*DOC:mgu|(unifEquWithInfo list) ref->unifTypeDefWithInfo list->unit|Fonction qui calcule
l'unificateur le plus général(principale) de l'ensemble d'equation p,
c'est le fruit de l'implémentation de toutes les règles, elle boucle
sur le problème p jusqu'a ce que aucune substitution n'est faite, ou
une exception est déclancher par une des règle, la référence p 
contient à la fin de l'execution l'unificateur principale
(le problème sous une forme résolu)*)
let rec mgu (p:(unifEquWithInfo list) ref) :unit= 
						try(
							p:=decomposeRule !p;
							p:=deleteRule !p;
							p:=orientRule !p ;
							p:=substitAndTestEnd !p;
							mgu p ;
							
						 )with
						 EndOfExec "noSubtitutionDone"->()
			;;

(*DOC:getVarVal|unifEquWithInfo list->unifTypeDefWithInfo|Fonction qui recherche dans un
unificateur p la valeur d'une variable v et la retourner, si elle n'existe
pas elle retournera une variable avec un id vide*)
let rec getVarVal (p:unifEquWithInfo list) (v:unifTypeDefWithInfo)=
	match p with
	[]->TypeVarExt ("",{localisation=Position(LigneCar(0,0),LigneCar(0,0))})
	|EqExt(t1,t2)::p1->if (discardTypeInfo t1=discardTypeInfo v) then t2 else getVarVal p1 v ;;

(*DOC:mguFindAndCheck|(unifEquWithInfo list) ref->unifTypeDefWithInfo list->bool|Fonction  qui
n'est qu'une extention de la fonction <mgu>, en plus de ce qu'offre <mgu> elle
capte les exceptions et gére les erreurs, elle retourne true si on a trouver 
l'unificateur, si non false*)
let mguFindAndCheck (p:(unifEquWithInfo list) ref)  :bool=
(* 	try(  *)
		let _= mgu p in let rec mguFindAndCheck p  = 
			match p with
			[]->true
			|EqExt(FExt(((x,y) as f),_),TypeVarExt(t,inf))::p1->raise (Failure ("Error "^(printInf inf)^"\n          This expression has type "^t^
										             "\n          This is not a function; it cannot be applied") 
										    )
			|_::p1->mguFindAndCheck p1 
				in mguFindAndCheck !p 
(* 		) *)
(* 	with *)
(* 	Failure "distinctTypeEquality"->print_string "Distinct types equality	!";print_newline ();flush stdout;false *)
(* 	|Failure "occurCheck"->print_string "Self application	!";print_newline ();flush stdout;false *)
(* 	|Failure "notResolvedEquation"->print_string "Can't find unifier to equation	!";print_newline ();flush stdout;false *)

(*DOC:insertIfNotExist|'a list -> 'a -> 'a list|Fonction qui prend en argument
une liste et un element,elle insere l'element à la fin de la liste s'il 
n'existe pas*)
let rec insertIfNotExist (l:'a list) elmnt :'a list=
	match l with
	[]->[elmnt]
	|x::l1->if (elmnt=x) then l else x::insertIfNotExist l1 elmnt;;

(*DOC:extractFromArrowForm|unifTypeDefWithInfo->unifTypeDefWithInfo list|Fonction qui permet
d'extraire l'ensemble des types élémentaires utilisés par un type composé,
par exemple le type (int->bool->int->float) donnera l'ensemble 
[int;bool;float]*)
let extractNames (t:unifTypeDefWithInfo) :string list=let typeList=ref [] in
	let rec extractFromArrowForm t=
		match t with
		(TypeVarExt (x,_)) -> if((isInternalVar x) || (isUserVar x )) then (let _ = typeList:= (insertIfNotExist (!typeList) x)  in !typeList)
			else !typeList
		|FExt((t1,t2),_)-> (let _=typeList:=extractFromArrowForm t1;typeList:=extractFromArrowForm t2 in !typeList)  
			in extractFromArrowForm t;;

let redistributeNames (namesList:string list) :(string*string) list =
	let rec redistributeNames namesList n=
		match namesList with
			[]->[]
			|x::l->(x,(genTypeName n User))::(redistributeNames l (n+1))
	in redistributeNames namesList 0;;
	
let rec printCouples s=
	match s with
	[]->""
	|(x,y)::l->print_string ("("^x^","^y^")");flush stdout;printCouples l;;
	
let rec findCorrespondence coupleList name=
	match coupleList with
	[]->""
	|(x,y)::l->if(x=name) then  y else findCorrespondence l name;; 


let rec applySubstitution subst t=
	match t with
		TypeVarExt (x,inf)->let newName=findCorrespondence subst x in  if(newName="") then (TypeVarExt (x,inf))
			else (TypeVarExt (newName,inf))
		|FExt((t1,t2),inf)->FExt((applySubstitution subst t1,applySubstitution subst t2),inf);;
		
let renameTypeVars t=
	let namesList=extractNames t in
	let substitution=redistributeNames namesList  in
	applySubstitution substitution t;;
