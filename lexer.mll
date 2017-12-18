    {
        open Lexing
        open Parser
        open String
        
        
        exception LexErr of string
        let error msg start finish  = 
                  Printf.sprintf "\nErreur Lexical ligne %d: caractère %d..%d): %s" start.pos_lnum 
            (start.pos_cnum -start.pos_bol) (finish.pos_cnum - finish.pos_bol) msg

        let lex_error lexbuf = 
            raise ( LexErr (error (lexeme lexbuf) (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)))
(*  Ces variables cert à définir quel token sera reconnu en étant dans un état particulier  *)
        let returnType_state : bool ref = ref false;;
        
        exception Erreur
        exception Eof
    }
(*   Identificateurs     *)
    let id  = ['a'-'z']['a'-'z''A'-'Z''0'-'9']*
    let typeName=(['a'-'z']+)|("'"['a'-'z']+)
(*   Nombres   *)
     let integer=['0'-'9']+
    let churchInteger='c'integer
    let real=integer '.' integer*
(*   Booleen   *)
     let boolean="true"|"false"
    
    rule token = parse
    |'\n'|'\t'          { Lexing.new_line (lexbuf);token lexbuf }
    |' '                { token lexbuf                          }
    |'\\'               { LAMBDA                                }
    |'('                { PO                                    }
    |')'                { PF                                    }
    |':'                { returnType_state:=true;Colon      }
    |"->"               { returnType_state:=true;Arrow      }
(*  Support des operateurs artithmitiques    *)
     |"+."      {REALPLUS}
     |"-."      {REALMINUS}
     |"*."      {REALMULT}
     |"/."      {REALDIV}
     |'+'       {INTPLUS}
     |'-'       {INTMINUS}
     |'*'       {INTMULT}
     |'/'       {INTDIV}
(*  Support des nombres    *)
    |churchInteger  as lx   { CINT(int_of_string (sub lx 1 ((length lx)-1))) }
    |real as lx             { REAL(string_of_float(float_of_string lx))      }
    |integer as lx          { INT(string_of_int(int_of_string lx))           }
    
    |'.'                        { POINT     }
    |'['                        { CO        }
    |']'                        { CF        }
    |','                        { VIRGULE   }
    |"\""                       { QUOTE     }
    |'S'                        { S         }
    |'K'                        { K         }
    |'I'                        { I         }
    |'B'                        { B         }
    |'C'                        { C         }
(*   Support des operateurs de comparaisons        *)
    |"=="                       { EQ            }
    |">"                        { HIGHERTHAN    }
    |"<"                        { LESSTHAN      }
(*  Support des operateurs booléens    *)   
    |"&&"                       { AND       }
    |"||"                       { OR        }
    |"not"                      { NOT       }
    
(*  valeurs de type bool    *)
     |boolean as lx             { BOOL(lx)  }
    |"let"                      { LET       }
    |"in"                       { IN        }
    |"rec"                      { REC       }
    |"load"                     { LOAD      }
    |"exit"                     { EXIT      }
    |"then"                     { THEN      }
    |"if"                       { IF        }
    |"else"                     { ELSE      }
    |"THEN"                     { L_THEN    }
    |"IF"                       { L_IF      }
    |"ELSE"                     { L_ELSE    }
    |"load_comb"                { LOADCOMB  }
    |"lambda_to_deb"            { LTD       }
    |"lambda_to_comb"           { LTC       }
    |"comb_to_lambda"           { CTL       }
    |"comb_to_deb"              { CTD       }
    |"deb_to_lambda"            { DTL       }
    |"deb_to_comb"              { DTC       }
    |"(*"                       { commentaire 0 lexbuf  }
    |'='                        { EQUAL                 }
    |';'                        { SEMIC                 }
    |typeName as name           { if(!returnType_state) then 
                                    (returnType_state:=false;OtherTypes name)
                                  else IDENT name   }
    |id         as lx           { IDENT(lx)         }
    |eof                        { EOF               }
    |_                          { lex_error lexbuf  }

    and commentaire niveau = parse
      "(*"  { commentaire (niveau + 1) lexbuf                                      }
      |"*)" { if niveau = 0 then token lexbuf else commentaire (niveau - 1) lexbuf }
      |eof  { EOF }
      |_    { commentaire niveau lexbuf }