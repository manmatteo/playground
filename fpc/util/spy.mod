module spy.

announce G :- print ">>" G, fail.
spy G :- (print ">Entering " G, G, print ">Success  " G;
          print ">Leaving  " G, fail).
