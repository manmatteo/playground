% 9 Jan 2018: Below is an early draft that encodes and checks expansion proofs.

module exp-examples.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate lkf-kernel.
accumulate exp-sk-fpc.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%  Declare here the print name and arity of function and predicate
%%%%  systems for the non-logical constants used in this file.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred_pname q'      "q'" [].
pred_pname (r' X)  "r'" [X].
pred_pname (s X)   "s" [X].

fun_pname  a'      "a'" [].
fun_pname  b'      "b'" [].
fun_pname (f' X)   "f'" [X].
fun_pname (f X)    "f"  [X].
%fun_pname (h' X Y) "h'" [X, Y].
%fun_pname (g X Y)  "g"  [X, Y].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eexample 1 (eC (eOr eLit eLit)) (or (ng q') q').

eexample 2 (eIntro x\ eC (eAll x (eOr eLit eLit)))
          (forall x\ or (r' x) (ng (r' x))).

% The drinker formula
eexample 3 (eIntro y\ eIntro z\ eC
          (eSome [(pr a' (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% Example 3 but with circular dependencies - this should fail to check.
eexample 4 (eIntro y\ eIntro z\ eC
          (eSome [(pr z  (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

eexample 5 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' a') (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted (and fails to check).
eexample 6 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The drinker formula with order
eexample 7 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr a' (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% Example 3 but with circular dependencies and order (fails)
eexample 8 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr z  (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% This is example 5 with order.
eexample 9 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' a') (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted but with order (fails).
eexample 10 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% DM: Zak reminded me that I should be careful with a block of
% existentials.  Delays are needed after each existential.

eexample 11 (eC
    (eOr eLit
         (eSomeOrd [(pr     a'  (eSomeOrd [(pr     (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
     (or (ng (r' (h'    a'  (f' a')))) (exists x\ exists y\ r' (h' x y))).

eexample 12 (eC
    (eOr eLit
         (eSomeOrd [(pr    a'  (eSomeOrd [(pr      (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
    (or (ng (r' (h' (f' a') (f' (f' a'))))) (exists x\ exists y\ r' (h' x y))).

% Skolemized versions of the previous examples (run them with :- test N.)
% skexample Tree SkF F

skexample 21 (eC (eOr eLit eLit))
             (or (ng q') q')
             (or (ng q') q').

skexample 22 (eC (eOr eLit eLit))
             (or (r' a') (ng (r' a')))
             (forall x\ or (r' x) (ng (r' x))).
             % (eIntro x\ eC (eAll x (eOr eLit eLit)))

% The drinker formula
skexample 23 (eC
           (eSome [(pr a' (eOr eLit eLit)),
                   (pr (f' a')  (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' (f' x)))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with order
skexample 27 (eC
          (eSomeOrd [(pr a' (eOr eLit eLit)),
                     (pr (f' a')  (eOr eLit eLit))]))
          (exists x\ or (ng (r' x)) (r' (f' x)))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with inner skolemization
skexample 30 (eC
           (eSome [(pr a' (eOr eLit eLit)),
                   (pr a'  (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' a'))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with inner skolemization
skexample 31 (eC
           (eSome [(pr a' (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' a'))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The "Double drinker formula"
skexample 32
(eC
       (eSome [(pr a' (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                              (pr (h' a' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))])),
          (pr (g a' b') (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                             (pr (h' a' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))]))]))
(exists y\ exists w\ (or (or (ng (r' (g y w))) (r' y)) (or (ng (s (h' y w))) (s w))))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (s z)) (s w)))).


% Double drinker formula with inner skolemization
skexample 33
(eC
       (eSome [(pr a' (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                              (pr (f' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))])),
          (pr (f a') (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                             (pr (f' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))]))]))
(exists y\ exists w\ (or (or (ng (r' (f y))) (r' y)) (or (ng (s (f' w))) (s w))))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (s z)) (s w)))).


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

% Translation from Expansion Tree of a Skolemized formula to Skolem-ET of the formula
% translate (SkolemizedFormula ExpTree    DeepF
%            OriginalFormula   SkolemTree DeepF')

% DM Extend translate to handle eSomeOrd also

% translate A B C D E F :- announce (translate A B C D E F).

translate F Q Dp
          (forall A) (eAll T Q') Dp' :- translate F Q Dp (A T) Q' Dp'.

translate (or A B) (eOr Q1 Q2)  (or Dp1 Dp2)
          (or A' B') (eOr Q1' Q2') (or Dp1' Dp2') :-
                                               translate A Q1 Dp1 A' Q1' Dp1',
                                               translate B Q2 Dp2 B' Q2' Dp2'.

translate (and A B) (eAnd Q1 Q2) (and Dp1 Dp2)
          (and A' B') (eAnd Q1' Q2') (and Dp1' Dp2') :-
                                               translate A Q1 Dp1 A' Q1' Dp1',
                                               translate B Q2 Dp2 B' Q2' Dp2'.

translate (exists F) (eSome [pr Term ET]) Dp
          (exists F') (eSome [pr Term ET']) Dp' :-
                                 translate (F Term) ET Dp (F' Term) ET' Dp'.

translate (exists F) (eSome ((pr Term ET)::Rest)) (or Dp1 Dp2)
          (exists F') (eSome ((pr Term ET')::Rest')) (or Dp1' Dp2') :-
                  translate (F Term) ET Dp1 (F' Term) ET' Dp1',
                  translate (exists F) (eSome Rest) Dp2 (exists F') (eSome Rest') Dp2'.

translate F eLit  F
          F eLit  F.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test I          :- eexample I Exp Form, polarize Form B, check_exp Exp B.

test I :- skexample I (eC Exp) SkForm Form,
%          translate SkForm Exp _ Form Exp' _,
          polarize Form B, check_exp (eC Exp) B.

check_exp (eC Exp) B :- lkf_entry (astate nil [pr B Exp]) B.
check_exp (eIntro Exp) B :- pi x\ check_exp (Exp x) B.

test_all :- eexample I Exp Form, polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Exp B, print "\n", fail.

test_all :- skexample I Exp _ Form, polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Exp B, print "\n", fail.

test_spec Exp B :- (check_exp Exp B, print "#", fail) ; true.
