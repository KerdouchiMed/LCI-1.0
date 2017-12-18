let b= ref ""

let _ = GMain.init ()

let window = GWindow.window 
 ~title:"LCi Interpreter V 0.2" 
 ~height:400
 ~width:600 
 ~resizable:true ()

(* Bouton qui souhaite le bonjour � l'utilisateur. *)
let uprint msg () =
  print_endline msg;
  flush stdout





let box = GPack.vbox ~homogeneous:false ~packing:window#add ()
 let menu_bar = GMenu.menu_bar ~height:20 ~width:600  ~packing:(box#pack ~expand:false ) () 
  let file_item = GMenu.menu_item ~label:"File" ~packing:menu_bar#append () 


let fixed = GPack.fixed ~packing:(box#pack ~expand:false) ()

 
  

(*let vbox = GPack.paned `VERTICAL ~height:300 ~width:600 ~packing:(fixed#put ~x:(0) ~y:(50)) () *)
let vbox = GPack.paned ~height:300 ~width:600 `VERTICAL ~packing:(box#pack ~expand:true ~fill:true ~padding:0) () 
(* let () = vbox#set_position(200)  *)


let scroll = GBin.scrolled_window
                 ~hpolicy:`AUTOMATIC ~vpolicy:`ALWAYS
                 ~packing:vbox#add () 

let scroll2 = GBin.scrolled_window
                 ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
                 ~packing:vbox#add ( )
let textview = GText.view ~editable:false ~packing:scroll#add_with_viewport ()  
    
let entry  = GText.view ~editable:true   ~packing:scroll2#add_with_viewport ()  

 
let lc_btn = GButton.radio_button ~label:"LC" ~active:true ~packing:(fixed#put ~x:(0) ~y:(22)) () 


  let comb_btn = GButton.radio_button ~group:lc_btn#group ~label:"COMB"
      ~active:false ~packing:(fixed#put ~x:(50) ~y:(22)) () 

  let deb_btn = GButton.radio_button
		~group:lc_btn#group ~label:"DEB" ~active:false ~packing:(fixed#put ~x:(120) ~y:(22)) () 




      let chechmet () = if lc_btn #active then "lc"
       else if comb_btn #active then "comb" else "deb"  

 
let hbox = GPack.button_box `HORIZONTAL
  ~layout:`EDGE (* C'est ici que l'on choisit la disposition des boutons. *)
  ~border_width:2
  ~packing:(box#pack ~expand:false)  ()



let evaluate = GButton.button
 ~label:"Evaluate"
 ~packing:hbox#add ()
let load_btn = GButton.button
  ~label:"Load"
  ~packing:hbox#add ()
  let show_fun = GButton.button
  ~label:"Display"
  ~packing:hbox#add ()

 let clear =  GButton.button
 ~label:"Clear"
 ~packing:hbox#add ()

let affiche_liste () = b := (!b)^"\n"^(Calc.show_enviro (!Global.functions)); textview#buffer#set_text !b

let scrldwn () = let ad = scroll#vadjustment in
                        let () = ad#set_value ( ad#upper) in
                          scroll#set_vadjustment ad


let file_ok_sel f ki () = 

  try
let tree = [(Lambda.Load f#filename)]  in b:= !b ^ (Calc.eval (tree) (chechmet()) ) ;   textview#buffer#set_text !b ; ki () ;  f#destroy () ;
with Lambda.ParseErr a -> b :=!b ^ a; textview#buffer#set_text !b


let load_file () = 
  let filew = GWindow.file_selection ~title:"File selection" ~border_width:10
    ~filename:"functions"  () in

  filew#set_destroy_with_parent false;
  filew#connect#destroy ~callback:filew#destroy ;
  
  filew#ok_button#connect#pressed ~callback: (file_ok_sel filew scrldwn ) ; 
 (* filew#ok_button#connect#released  ~callback: (filew#destroy )  ;*)


  filew#cancel_button#connect#clicked ~callback:filew#destroy;

    
  filew#show () 


(* Fonction qui affiche le message sur stdout. *)
let cls () = textview#buffer#set_text ""; b := "" ; entry#buffer#set_text ""
let parse str = 
  try
    let lb = Lexing.from_string (entry#buffer#get_text ()^";;") 
    
    in
      try (Calc.eval (Calc.interpreteur lb) (chechmet ()))
      with Lambda.ParseErr a -> a 
          
with Lexer.LexErr a -> a


let create_menu ~packing () =
  let file_menu = GMenu.menu ~packing () in
  let item = GMenu.menu_item ~label:"Open" ~packing:file_menu#append () in
  item#connect#activate ~callback:load_file ; 
  let item = GMenu.menu_item ~label:"Quit" ~packing:file_menu#append () in
  item#connect#activate ~callback:GMain.Main.quit

 (*let menu_bar = GMenu.menu_bar ~height:20 ~width:600  ~packing:(fixed#put ~x:(0) ~y:(0)) () *)



  
  
  
 let print_hello ()  =
let start = Sys.time () in 
  let sh = parse (entry#buffer#get_text ()) in
                   let () = b := (!b)^"\n" ^ (entry#buffer#get_text ())^ sh^"\nexecution time : "^string_of_float (Sys.time ()-.start)^"\n" in 
                      let () = textview#buffer#set_text !b; (*print_string (textview#buffer#get_text ()); flush stdout*) in
                       scrldwn ();;



let _ = 
 window#connect#destroy ~callback:GMain.quit;
create_menu ~packing:file_item#set_submenu () ;
 evaluate#connect#clicked ~callback:print_hello;
 load_btn#connect#clicked ~callback: load_file;
 show_fun#connect#clicked ~callback: affiche_liste;
 clear#connect#clicked ~callback:cls;
  let () = b := !b ^"LCi ver 0.2\n" in  
    let llb = Lexing.from_string "load \"library\";;" in
      let _ = (Calc.eval (Calc.interpreteur llb) (chechmet ())) in
      
  textview#buffer#set_text !b ;
   entry#buffer#set_text "enter an expression ! "  ;
 window#show ();
 GMain.main ()
