ocamlyacc -v parser.mly
ocamllex lexer.mll
ocamlc -c global.ml
ocamlc -c lowLevelLibrary.ml
ocamlc -c lambda.ml 
ocamlc -c parser.mli parser.ml
ocamlc lexer.ml

ocamlc -c unificationAlgorithm.ml
ocamlc -c inferenceMechanism.ml

ocamlc -c combinator.ml
ocamlc -c debruijn.ml

ocamlc -c calc.ml

ocamlc -w s -o LCi -I +lablgtk2 lablgtk.cma global.cmo lowLevelLibrary.cmo lambda.cmo lexer.cmo parser.cmo debruijn.cmo combinator.cmo unificationAlgorithm.cmo inferenceMechanism.cmo calc.cmo test.ml

rm *.cmo *.cmi *.mli parser.ml lexer.ml