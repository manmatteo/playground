module util.

type bracket          string -> prop -> string -> prop.  % Auxiliary

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.

announce G :- bracket ">>" G "\n", fail.

spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).

split [] [] [].
split [(pr A1 A2) | In] [A1 | Out1] [A2 | Out2] :-
  split In Out1 Out2.
  
type debugmap list A -> (A -> B -> prop) -> list B -> prop.
debugmap X Y Z :- print "map" X Y Z, fail.
debugmap [] _ [].
debugmap [X|XS] F L :- print (F X Y), F X Y, print Y, L = [Y|YS], print "done", debugmap XS F YS.

memb_and_rest [A|List] A List.
memb_and_rest [A|List] B [A|List'] :- not (A = B), memb_and_rest List B List'.
