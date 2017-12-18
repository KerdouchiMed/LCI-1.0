open Global
let interpreteur lexbuffer =   Parser.instruction Lexer.token lexbuffer



let add x e = 
  if List.mem_assoc x !functions then 
    functions := (x, e)::(List.remove_assoc x !functions)
  else 
    functions := (x, e)::!functions
      
let rec exploiter arbre liste =  
  match arbre with
  |Global.Var x -> 
    if List.mem_assoc x !functions && not(List.exists ((fun a b -> a = b) x) liste) then 
       exploiter (List.assoc x !functions) liste 
    else 
       Global.Var x
  |Global.CInt n -> Lambda.ofInt n
  |Global.App (m, n) -> Global.App(exploiter m liste, exploiter  n liste)
  |Global.Abs (x, m) -> Global.Abs(x, exploiter m (x::liste))
	
exception NotFound
let rec existExp exp lst_fun=
	match lst_fun with
	|[] -> raise NotFound
	|(x, e)::l -> if Lambda.unify e = exp then (Global.Var x) else existExp exp l 


let treat expWithInfo env meth = 
	let exp=discardInfo expWithInfo in
	let t = (exploiter  exp []) in
	let ut = (Lambda.unify t) in 
	let typ = (InferenceMechanism.main expWithInfo env) in
    "\n\nExpression > " ^ (Lambda.toString  ut)
    ^(if (!InferenceMechanism.typed) = false  then ("\n"^typ) 
    else (
	if meth = "lc" then ( 
		"\nType > "^(typ)
		^"\nReduction > "^(Lambda.print_lreduce ut))
						
	else if meth = "comb" then (
		"\nType > "^(typ)
		^"\nCLterme Reduction > " ^ (Combinator.print_cl_reduce t)
							 )
	else  if meth = "deb" then ( 
		"\nType > "^(typ)
		^"\nReduce Debruijn > " ^ (Debruijn.print_deb_reduce (Debruijn.deb t))
							 )
	else "\n\n\nError :p" 
      )^("\nCorrespondance > "^(Lambda.toString(let e = ut in try  existExp e !functions with |NotFound -> Global.Var "Non trouvé"))^"\n"))




let rec show_enviro l = match l with 
[] -> ""
|(a,b)::c ->  let f =  (Lambda.unify (exploiter b [])) in "\nDeclaration > " ^ a ^ " : " ^ (Lambda.toString f)^ "\n" ^(show_enviro c)




let rec eval2 lisAst meth = match lisAst with
  |[] -> [""]
  |a::l -> match a with 
	|Lambda.Exp(env, m) -> let treatExp = (treat m env meth) in
				[treatExp]@( eval2 l meth )
	|Lambda.Declaration (env,(x, eInf)) ->if(List.exists (fun z->z=x) !protectedIdents) then ["\n"^ x ^ " : This identifier is reserved !"]@ (eval2 l meth) else let e = discardInfo eInf 
					in let typfct = discardTypeInfo (try (InferenceMechanism.giveMeTheType (eInf) env) 
								      with UnificationAlgorithm.Failure s ->Global.(TypeVarExt (s,getExpInfo eInf)))
					in if((!InferenceMechanism.typed)=true ) then
						let _ = Global.funType:= InferenceMechanism.insertTypSansRep (x,typfct) !Global.funType
						in [ let f =  (Lambda.unify (exploiter e [])) 
						      in let () = add x f 
						      in "\n\nDeclaration > " ^ x ^ " : " ^ (Lambda.toString f) 
							^"\nType > "^ (InferenceMechanism.typeToString (typfct))
						   ] @ (eval2 l meth)
					 else  ["\n"^InferenceMechanism.typeToString ((typfct))] @ (eval2 l meth)
					 
	|Lambda.RecDeclaration (env,(x, eInf)) ->if(List.exists (fun z->z=x) !protectedIdents) then ["\n"^ x ^ " : This identifier is reserved !"]@ (eval2 l meth) else
					let e =discardInfo eInf 
					in let expInf=(Global.AppExt(((Global.VarExt("fix",getExpInfo eInf)), (Global.AbsExt((x, eInf),getExpInfo eInf))),(getExpInfo eInf)))
					in let exp = discardInfo expInf 
					in let typfct = discardTypeInfo(try (InferenceMechanism.giveMeTheType (expInf) env) 
							    with UnificationAlgorithm.Failure s ->Global.(TypeVarExt (s,getExpInfo eInf)))
					in if((!InferenceMechanism.typed)=true ) then
						let _ = Global.funType:= InferenceMechanism.insertTypSansRep (x,typfct) !Global.funType
						in [ let f = Lambda.unify (exploiter exp [])
							in let () = add x f in "\n\nRecDeclaration > " ^ x ^ " : " ^ (Lambda.toString f)
							^"\nType > "^ (InferenceMechanism.typeToString (typfct))
						   ] @(eval2 l meth) 
					else  ["\n"^InferenceMechanism.typeToString ((typfct))] @ (eval2 l meth)
					
	|Lambda.Load file -> 
			if Sys.file_exists (file^".lc") then
				(["\nFichier " ^ file ^ " > \n"] @ (eval2 (interpreteur (Lexing.from_channel (open_in (file ^ ".lc")) )) meth)) @ (eval2 l meth) @ ["\nFile is loaded \n"]
			else
		if Sys.file_exists (file) then 
		(["\nFichier " ^ file ^ " > \n"] @ (eval2 (interpreteur (Lexing.from_channel (open_in (file)) )) meth)) @ (eval2 l meth) @ ["\nFile is loaded \n"]
		else
      				(["\nFichier : " ^ (file^".lc")] @ [" est introuvable\n"]) @ (eval2 l meth)

	|Lambda.Exit -> let () = exit 0 in []
	|Lambda.LTD eInf ->let e=discardInfo eInf in ["Conversion Lambda -> Debruijn : "] @ [(Debruijn.toStringDeb (Debruijn.deb (exploiter e [])))]@  (eval2 l meth)
	|Lambda.LTC eInf ->let e=discardInfo eInf in ["Conversion Lambda -> Combinateur : "] @ [(Combinator.toStringCl (Combinator.cl_make (exploiter e [])))] @ (eval2 l meth)
	|_ -> []


let rec eval3 ast = 
	match ast with
	| [] -> ""
	| a::b -> a ^ (eval3 b)

let eval ast meth= 
	eval3 (eval2 ast meth) 
