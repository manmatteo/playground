module dd-examples.
accumulate lib.
accumulate classical.
accumulate classical-examples.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate dd-fpc.
accumulate ded-fpc.

polarize A      L :- pred_pname A Name Args, lit+ (atom Name Args) L.
polarize (ng A) L :- pred_pname A Name Args, lit- (atom Name Args) L.
polarize tt               A :- true-  A.
polarize ff               A :- false- A.
polarize (and B C)        A :- polarize B D, polarize C E, conj- D E A.
polarize (or  B C)        A :- polarize B D, polarize C E, disj- D E A.
polarize (imp B C)        A :- polarize (ng B) D, polarize C E, disj- D E A.
polarize (equiv B C)      A :- polarize (imp B C) D, polarize (imp C B) E, conj- D E A.
polarize (ng (ng B))      C :- polarize B C.
polarize (ng (and B C))   A :- polarize (ng B) D, polarize (ng C) E, disj- D E A.
polarize (ng (or  B C))   A :- polarize (ng B) D, polarize (ng C) E, conj- D E A.
polarize (ng (imp B C))   A :- polarize B D,      polarize (ng C) E, conj- D E A.
polarize (ng (equiv B C)) A :- polarize (ng (imp B C)) D, 
                               polarize (ng (imp C B)) E, disj- D E A.
polarize (forall B)      A :- (pi x\ polarize (B x) (D x)),      all-  D A.
polarize (ng (exists B)) A :- (pi x\ polarize (ng (B x)) (D x)), all-  D A.
polarize (exists B)      A :- (pi x\ polarize     (B x)  (D x)), some+ D A.
polarize (ng (forall B)) A :- (pi x\ polarize (ng (B x)) (D x)), some+ D A.

check_small_dd B :- polarize B B', lkf_entry (dd (succ zero)) B'.

test_all :- 
   example X F, 
   (sigma Str\ term_to_string X Str, print Str, print " "),
   if (check_small_dd F)
      (print "Success\n") 
      (print "Fail\n"), 
  fail.
