module geom-examples.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate geom-fpc.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%  Declare here the print name and arity of function and predicate
%%%%  systems for the non-logical constants used in this file.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred_pname (r X Y)  "r" [X, Y].
pred_pname (q X)  "q" [X].
pred_pname (s X Y)  "s" [X, Y].

fun_pname a "a" [].
fun_pname n1 "n1" [].
fun_pname n2 "n2" [].
fun_pname n3 "n3" [].
fun_pname n4 "n4" [].
fun_pname n5 "n5" [].
fun_pname  b      "b" [].
fun_pname  c      "c" [].
fun_pname (f X)   "f" [X].
%fun_pname (h X Y) "h" [X, Y].
%fun_pname (g X Y) "g" [X, Y].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

% The follow uses of delay- breaks up a sequence of existentials.
polarize (exists B)      A :- (pi x\ delay-       (B x)  (D x)), some+ D A.
polarize (ng (forall B)) A :- (pi x\ delay-   (ng (B x)) (D x)), some+ D A.

delay-   B D :- polarize B C, false- False, disj- False C D.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test I          :- example I List Form, polarize Form B, check_geom List B.

check_geom List B :- lkf_entry (astate nil nil List) B.

test_all :- example I List Form, polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec List B, print "\n", fail.

test_spec List B :- (check_geom List B, print "#", fail) ; true.

example 31
  [1,2]
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r y z) (r x z))))
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r x z) (exists w\ (and (r y w) (r z w))))))
  (imp (r n1 n2)
  (imp (r n1 n5)
  (exists u\ (and (r n2 u) (r n5 u))))))).

% gexample 1
example 1
[1]
(imp
(forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (exists w\ and (r y w) (r z w))))
(imp (and (r a b) (r a c))
(exists X\ and (r b X) (r c X)))).
%% Trying an example inspired by modal logic
%% Original formula
% (forall x\ forall y\ forall z\ (or  (and (ng (s x y)) (ng (s x z))) (exists w\ (and (s y w) (s z w)))))
% (forall x\ forall y\ forall z\ (or (or (ng (s x y)) (ng (s y z))) (s x z) ))
% (and (s a b) (and (s b c) (and (s c d) (s a e))))
% (exists f\ (and (s d f) (s e f)))
% NNF
% (exists x\ exists y\ exists z\ (and  (or (s x y) (s x z)) (forall w\ (or (ng (s y w)) (ng (s z w))))))
% (exists x\ exists y\ exists z\ (and (and (s x y) (s y z)) (ng (s x z)) ))
% (or (ng (s a b)) (or (ng (s b c)) (or (ng (s c d)) (ng (s a e)))))
% (exists f\ (and (s d f) (s e f)))


% (or (exists x\ exists y\ exists z\ (and  (or (s x y) (s x z))
%                                          (forall w\ (or (ng (s y w)) (ng (s z w))))))
%     (or (exists x\ exists y\ exists z\ (and (and (s x y) (s y z)) (ng (s x z)) ))
%         (or (or (ng (s a b))
%                 (or (ng (s b c)) (or (ng (s c d)) (ng (s a e)))))
%             (exists f\ (and (s d f) (s e f))))))

% (eOr (eSome [(pr TERM_X1 (eSome [(pr TERM_Y1 (eSome [(pr TERM_Z1 (eAnd (eOr eLit eLit)
%                                                                  (eAll w (eOr eLit eLit)) ))]))] ))])
%      (eOr (eSome [(pr TERM_X1 (eSome [(pr TERM_Y1 (eSome [(pr TERM_Z1 (eAnd (eAnd eLit eLit) eLit))]))]))])
%           (eOr (eOr eLit
%                     (eOr eLit (eOr eLit eLit)))
%                 )





%% Given F and its skolemization sk(F), translate an ET of sk(F) into a Skolem-ET of F

% type eIntro            (i -> qet) -> qet.
% type eC                et -> qet.

% type eTrue, eFalse     et.
% type eLit              et.
% type eAnd, eOr	       et -> et -> et.
% type eAll              i  -> et -> et.	
% type eSome             subExp    -> et.
% type eSomeOrd          subExp    -> et.

%translate SkF (eC Q)  Dp
%          F   (eC Q) Dp :- translate SkF Q  Dp F Q Dp.

% translate F Q Dp
%           (forall A) (eAll T Q) Dp' :- translate F Q Dp (A T) Q' Dp'.
%                                         %translate F Q Dp (A T) Q' Dp'.

% translate (or A B) (eOr Q1 Q2)  (or Dp1 Dp2)
%           (or A' B') (eOr Q1' Q2') (or Dp1' Dp2') :-
%                                                translate A Q1 Dp1 A' Q1' Dp1',
%                                                translate B Q2 Dp2 B' Q2' Dp2'.
%                                                %translate A Q1 Dp1 A' Q1 Dp1',
%                                                %translate B Q2 Dp2 B' Q2 Dp2'.
% translate (and A B) (eAnd Q1 Q2) (and Dp1 Dp2)
%           (and A' B') (eAnd Q1' Q2') (and Dp1' Dp2') :- translate A Q1 Dp1 A' Q1' Dp1',
%                                                       translate B Q2 Dp2 B' Q2' Dp2'.

% translate (exists F) (eSome [pr Term ET]) Dp
%           (exists F') (eSome [pr Term ET']) Dp' :-
%                                  translate (F Term) ET Dp (F' Term) ET' Dp',
%                                  translate (F Term) ET Dp (F' Term) ET' Dp'.

% translate (exists F) (eSome ((pr Term ET)::Rest)) (or Dp1 Dp2)
%           (exists F') (eSome ((pr Term ET')::Rest')) (or Dp1' Dp2') :-
%                   translate (F Term) ET Dp1 (F' Term) ET' Dp1',
%                   translate (exists F) (eSome Rest) Dp2 (exists F') (eSome Rest') Dp2'.


% translate (exists F) (eSomeOrd [pr Term ET]) Dp
%           (exists F') (eSomeOrd [pr Term ET']) Dp' :-
%                                  translate (F Term) ET Dp (F' Term) ET' Dp',
%                                  translate (F Term) ET Dp (F' Term) ET' Dp'.

% translate (exists F) (eSomeOrd ((pr Term ET)::Rest)) (or Dp1 Dp2)
%           (exists F') (eSomeOrd ((pr Term ET')::Rest')) (or Dp1' Dp2') :-
%                   translate (F Term) ET Dp1 (F' Term) ET' Dp1',
%                   translate (exists F) (eSomeOrd Rest) Dp2 (exists F') (eSomeOrd Rest') Dp2'.

% translate F eLit  F
%           F eLit  F. % :- print "lit", term_to_string F Str, print Str.

% translate (exists x\ or (ng (r' x)) (r' (f x))) (eSome [(pr a' (eOr eLit eLit)), (pr (f a')  (eOr eLit eLit))]) Deep1 (exists x\ forall y\ or (ng (r' x)) (r' y)) T Deep2.

% translate (or (ng (r' a')) (r' (f a'))) (eOr eLit eLit)  (or Dp1 Dp2) (or A' B') (eOr eLit eLit) (or Dp1' Dp2').

