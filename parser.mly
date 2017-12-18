%{
	open Lexing
	open Parsing
	open Global
	let print_error () =
let pos = Parsing.symbol_start_pos () in
let pos2 = Parsing.symbol_end_pos () in
let lineNum = pos.pos_lnum in
let car1 = (pos.pos_cnum - pos.pos_bol) in
let car2 = (pos2.pos_cnum - pos2.pos_bol) in
(* let name = pos2.pos_fname in *)
Printf.sprintf "\nErreur Syntaxique Ligne %d, Caractère : %d to %d " lineNum car1 car2 (*(lexeme lexbuf)*)

(*Cette fonction permet de retourner la position d'une expression dans le flux en cours d'analyse*)
let getExpPosition ()= let pos = Parsing.symbol_start_pos () in
		let pos2 = Parsing.symbol_end_pos () in
		let car1 = (pos.pos_cnum - pos.pos_bol) in
		let car2 = (pos2.pos_cnum - pos2.pos_bol)
		in Global.Position(LigneCar(pos.pos_lnum,car1),LigneCar(pos2.pos_lnum,car2))

(*Cette fonction génère une structure qui contient des informations sur une expression*)
let genInf ()= 
	{localisation = getExpPosition ()}
		
%}

%token <int> CINT
%token <string> INT
%token <string> REAL
%token <string> BOOL
%token <string> IDENT 
%token <string>OtherTypes  
%token EOF LOAD QUOTE LTD LTC CTD CTL DTL DTC LOADCOMB S K B I C EQUAL LET EXIT LAMBDA PO AND OR EQ NOT PF POINT  IN  SEMIC REC IF THEN ELSE L_IF L_THEN L_ELSE CO CF VIRGULE
%token NEG INTPLUS INTMINUS INTMULT INTDIV REALPLUS REALMINUS REALMULT REALDIV
%token HIGHERTHAN LESSTHAN

%token Arrow Colon


%nonassoc PRECERROR
%nonassoc PRECABS
%right IF THEN ELSE L_IF L_THEN L_ELSE
%right Arrow
%left OR
%left AND
%right NOT
%left EQ HIGHERTHAN LESSTHAN


%right LAMBDA 
%right B S I K C PO CINT IDENT LET CO INT REAL BOOL
/*Operateurs arithmitiques*/
%right NEG
%left INTPLUS INTMINUS REALMINUS REALPLUS 
%left INTMULT INTDIV REALMULT REALDIV


%left PRECARITHM
%left PRECAPP




%start instruction
%type <Lambda.instruction list> instruction

%%

  
instruction:
   declaration SEMIC instruction { $1::$3 }
   |expression SEMIC instruction { let env=(!Global.envc) in let _ = Global.envc:=[] in (Lambda.Exp (env,$1))::$3 }
  |LOAD QUOTE IDENT QUOTE SEMIC instruction { (Lambda.Load $3)::$6 }
  |LTD expression SEMIC { [Lambda.LTD $2] }
  |LTC expression SEMIC { [Lambda.LTC $2] }
  |DTC expression SEMIC { [Lambda.DTC $2] }
  |DTL expression SEMIC { [Lambda.DTL $2] }
  |CTL expression SEMIC { [Lambda.CTL $2] }
  |CTD expression SEMIC { [Lambda.CTD $2] }
  |EXIT { [Lambda.Exit] }
  |SEMIC { [] }
  |EOF { [] }
  |error { raise (Lambda.ParseErr (print_error ()))}  
  ;
	
declaration:
    LET IDENT EQUAL expression {let env=(!Global.envc) in let _ = Global.envc:=[] in (Lambda.Declaration(env,($2, $4))) }
    |LET REC IDENT EQUAL expression {let env=(!Global.envc) in let _ = Global.envc:=[] in (Lambda.RecDeclaration(env,($3, $5))) }
    |erreursLet { $1 }
  ;
  
expression: 

simple {(*let _ = print_string "\nin parser : ";printInf (getExpInfo $1) ; print_string "\nendParser" in*) $1  }
|arithmeticExp %prec PRECARITHM {$1}
|booleanExp {$1}
/*|expression OR expression 	{ Global.AppExt((Global.AppExt((Global.VarExt ("or",(genInf())), $1),(genInf())), $3),(genInf())) }
	 |expression AND expression 	{ Global.AppExt((Global.AppExt((Global.VarExt ("and",(genInf())), $1),(genInf())), $3),(genInf())) }
	 |NOT expression 					{ Global.AppExt((Global.VarExt ("neg",(genInf())), $2),(genInf())) }*/

	|expression expression %prec PRECAPP { Global.AppExt(($1, $2),(genInf())) }
	|PO expression PF {$2}
	/*|erreursExp { $1 }*/
  ;
simple:
	

	IDENT 						{ Global.VarExt ($1,(genInf())) }
	|IDENT Colon idType	 	{( 
									 match ($3) with 
								    (Global.Type t) -> (Global.envc:=($1,t)::!Global.envc)
								    |_  -> ()
									 );Global.VarExt ($1,(genInf()))}
	|S 						{ Global.VarExt ("S",(genInf())) }
	|K 						{ Global.VarExt ("K",(genInf())) }
	|I 						{ Global.VarExt ("I",(genInf())) }
	|B 						{ Global.VarExt ("B",(genInf())) }
	|C 						{ Global.VarExt ("C",(genInf())) }
	|CINT 						{Global.CIntExt ($1,(genInf()))}
	|LAMBDA liste POINT expression %prec PRECABS { (Lambda.abstraction $2 $4 (genInf())) }
	|PO couple PF 					{ $2 }
	|L_IF expression L_THEN expression L_ELSE expression 	{ Global.AppExt((Global.AppExt(($2, $4),(genInf())), $6),(genInf()))}
	|IF expression THEN expression ELSE expression 			{ Global.AppExt((Global.AppExt((AppExt((VarExt ("ifElse",genInf()),$2),genInf()), $4),(genInf())), $6),(genInf()))}
	|LET IDENT EQUAL expression IN expression %prec PRECARITHM	{ Global.AppExt((Global.AbsExt(($2, $6),(genInf())), $4),(genInf())) }
	|LET REC IDENT EQUAL expression IN expression %prec PRECARITHM	{let exp = (Global.AppExt(((Global.VarExt("fix",genInf())), (Global.AbsExt(($3, $5),genInf()))),(genInf()))) in
																						Global.AppExt((Global.AbsExt(($3, $7),(genInf())), exp),(genInf()))}
	|CO list_exp CF 				{ $2 }
	/*|arithmeticExp  { $1 }*/
	;
list_exp:
								{ Global.VarExt ("nil",(genInf()))}
	|expression 			{ Global.AppExt((Global.AppExt((Global.VarExt ("cons",(genInf())), $1),(genInf())),(Global.VarExt ("nil",(genInf())))),(genInf())) }
	|expression SEMIC list_exp  { Global.AppExt((Global.AppExt((Global.VarExt ("cons",(genInf())), $1),(genInf())), $3),(genInf()))}
	;
couple:
	|expression VIRGULE expression { Global.AppExt((Global.AppExt((Global.VarExt ("pair",(genInf())), $1),(genInf())),$3),(genInf()))}
	;

liste:
   IDENT { [$1] }
  |liste IDENT { $1 @ [$2] }
  ;
booleanExp:
  BOOL	{ (Global.envc:=($1,TypeVar "bool")::!Global.envc);VarExt ($1,genInf()) }
  |expression OR expression 	{ Global.AppExt((Global.AppExt((Global.VarExt ("||",(genInf())), $1),(genInf())), $3),(genInf())) }
  |expression AND expression 	{ Global.AppExt((Global.AppExt((Global.VarExt ("&&",(genInf())), $1),(genInf())), $3),(genInf())) }
  |NOT expression 					{ Global.AppExt((Global.VarExt ("not",(genInf())), $2),(genInf())) }
  |expression EQ expression	{Global.AppExt((Global.AppExt((Global.VarExt ("==",(genInf())), $1),(genInf())), $3),(genInf())) }
  |expression HIGHERTHAN expression  {Global.AppExt((Global.AppExt((Global.VarExt (">",(genInf())), $1),(genInf())), $3),(genInf())) }
  |expression LESSTHAN expression	 {Global.AppExt((Global.AppExt((Global.VarExt ("<",(genInf())), $1),(genInf())), $3),(genInf())) }
  ;
arithmeticExp:
	REAL														{(Global.envc:=($1,TypeVar "real")::!Global.envc);VarExt ($1,genInf())}
	|INT														{(Global.envc:=($1,TypeVar "int")::!Global.envc);VarExt ($1,genInf())}
	|expression INTPLUS expression {AppExt((AppExt((VarExt("+",genInf()),$1),genInf()),$3) ,genInf())}
   |expression INTMINUS expression {AppExt((AppExt((VarExt("-",genInf()),$1),genInf()),$3) ,genInf())}
   |expression INTMULT expression	{AppExt((AppExt((VarExt("*",genInf()),$1),genInf()),$3) ,genInf())}
   |expression INTDIV expression	{AppExt((AppExt((VarExt("/",genInf()),$1),genInf()),$3) ,genInf())}
   |expression REALPLUS expression {AppExt((AppExt((VarExt("+.",genInf()),$1),genInf()),$3) ,genInf())}
   |expression REALMINUS expression {AppExt((AppExt((VarExt("-.",genInf()),$1),genInf()),$3) ,genInf())}
   |expression REALMULT expression {AppExt((AppExt((VarExt("*.",genInf()),$1),genInf()),$3) ,genInf())}
   |expression REALDIV expression	{AppExt((AppExt((VarExt("/.",genInf()),$1),genInf()),$3) ,genInf())}
   |INTMINUS expression 		{AppExt((AppExt((VarExt ("*",genInf()),$2),genInf()),VarExt ("-1",genInf())),genInf())}
   |REALMINUS expression {AppExt((AppExt((VarExt ("*.",genInf()),$2),genInf()),VarExt ("-1.",genInf())),genInf())}
  ;


  
erreursExp:
	|LAMBDA POINT expression %prec PRECERROR{ raise (Lambda.ParseErr ((print_error ())^" variable(s) oubliée(s) ")) }
	|LAMBDA expression %prec PRECERROR{ raise (Lambda.ParseErr ((print_error ())^" . oublié "))}
	|liste POINT expression %prec PRECERROR{ raise (Lambda.ParseErr ((print_error ())^" \206\187 oublié ")) }
;
erreursLet:
 LET IDENT EQUAL { raise (Lambda.ParseErr ((print_error ())^" \206\187-terme manque après = ")) }
|LET IDENT expression { raise (Lambda.ParseErr ((print_error ())^" = oublié")) }
|LET EQUAL expression { raise (Lambda.ParseErr ((print_error ())^" nom de la fonction oublié"))}
|LET REC IDENT EQUAL { raise (Lambda.ParseErr ((print_error ())^" \206\187-terme manque après = ")) }
|LET REC IDENT expression { raise (Lambda.ParseErr ((print_error ())^" = oublié")) }
|LET REC EQUAL expression { raise (Lambda.ParseErr ((print_error ())^" nom de la fonction oublié"))}
;

idType:	/*(*term type definition*)*/
	PO idType PF					{ $2 }
	|idType Arrow idType				{ match ($1,$3) with 
									(Global.Type t1,Global.Type t2) -> Global.Type(Global.F(t1,t2))
									|_-> Global.Unit ()
							}
	|typeName 					{ $1 }
;

typeName:
OtherTypes {Global.Type(Global.TypeVar $1)}
;	