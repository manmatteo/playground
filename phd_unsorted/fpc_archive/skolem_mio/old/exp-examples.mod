% 9 Jan 2018: Below is an early draft that encodes and checks expansion proofs.

module exp-examples.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate exp-fpc.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%  Declare here the print name and arity of function and predicate
%%%%  systems for the non-logical constants used in this file.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred_pname q'      "q'" [].
pred_pname (r' X)  "r'" [X].
pred_pname (q X)  "q" [X].
pred_pname (s' X Y)  "s'" [X, Y].

fun_pname  a'      "a'" [].
fun_pname  b'      "b'" [].
fun_pname  c'      "c'" [].
fun_pname (f' X)   "f'" [X].
%fun_pname (h' X Y) "h'" [X, Y].
%fun_pname (g X Y) "g" [X, Y].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

example 1 (eC (eOr eLit eLit)) (or (ng q') q').

example 2 (eIntro x\ eC (eAll x (eOr eLit eLit)))
          (forall x\ or (r' x) (ng (r' x))).

% The drinker formula
example 3 (eIntro y\ eIntro z\ eC
          (eSome [(pr a' (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% Example 3 but with circular dependencies - this should fail to check.
example 4 (eIntro y\ eIntro z\ eC
          (eSome [(pr z  (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

example 5 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' a') (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted (and fails to check).
example 6 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The drinker formula with order
example 7 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr a' (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% Example 3 but with circular dependencies and order (fails)
example 8 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr z  (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% This is example 5 with order.
example 9 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' a') (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted but with order (fails).
example 10 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% DM: Zak reminded me that I should be careful with a block of
% existentials.  Delays are needed after each existential.

example 11 (eC
    (eOr eLit
         (eSomeOrd [(pr     a'  (eSomeOrd [(pr     (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
     (or (ng (r' (h'    a'  (f' a')))) (exists x\ exists y\ r' (h' x y))).

example 12 (eC
    (eOr eLit
         (eSomeOrd [(pr    a'  (eSomeOrd [(pr      (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
    (or (ng (r' (h' (f' a') (f' (f' a'))))) (exists x\ exists y\ r' (h' x y))).

% Adding examples with Herbrand disjunctions
% example 13 (eC
%     (eSome [(pr bbb),
%             (pr ),
%             (pr )]
%     ))
%     (exists x\ )

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

test I          :- example I Exp Form, polarize Form B, check_exp Exp B.

check_exp (eC Exp) B :- lkf_entry (astate nil nil [pr B Exp]) B.
check_exp (eIntro Exp) B :- pi x\ check_exp (Exp x) B.

test_all :- example I Exp Form, polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Exp B, print "\n", fail.

test_spec Exp B :- (check_exp Exp B, print "#", fail) ; true.

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
%          F   (eC Q) Dp' :- translate SkF Q  Dp F Q Dp'.

translate F Q Dp
          (forall A) (eAll T Q') Dp' :- translate F Q Dp (A T) Q' Dp'.
                                        %translate F Q Dp (A T) Q' Dp'.

translate (or A B) (eOr Q1 Q2)  (or Dp1 Dp2)
          (or A' B') (eOr Q1' Q2') (or Dp1' Dp2') :-
                                               translate A Q1 Dp1 A' Q1' Dp1',
                                               translate B Q2 Dp2 B' Q2' Dp2'.
                                               %translate A Q1 Dp1 A' Q1 Dp1',
                                               %translate B Q2 Dp2 B' Q2 Dp2'.
translate (and A B) (eAnd Q1 Q2) (and Dp1 Dp2)
          (and A' B') (eAnd Q1' Q2') (and Dp1' Dp2') :- translate A Q1 Dp1 A' Q1' Dp1',
                                                      translate B Q2 Dp2 B' Q2' Dp2'.

translate (exists F) (eSome [pr Term ET]) Dp
          (exists F') (eSome [pr Term ET']) Dp' :-
                                 translate (F Term) ET Dp (F' Term) ET' Dp',
                                 translate (F Term) ET Dp (F' Term) ET' Dp'.

translate (exists F) (eSome ((pr Term ET)::Rest)) (or Dp1 Dp2)
          (exists F') (eSome ((pr Term ET')::Rest')) (or Dp1' Dp2') :-
                  translate (F Term) ET Dp1 (F' Term) ET' Dp1',
                  translate (exists F) (eSome Rest) Dp2 (exists F') (eSome Rest') Dp2'.


translate (exists F) (eSomeOrd [pr Term ET]) Dp
          (exists F') (eSomeOrd [pr Term ET']) Dp' :-
                                 translate (F Term) ET Dp (F' Term) ET' Dp',
                                 translate (F Term) ET Dp (F' Term) ET' Dp'.

translate (exists F) (eSomeOrd ((pr Term ET)::Rest)) (or Dp1 Dp2)
          (exists F') (eSomeOrd ((pr Term ET')::Rest')) (or Dp1' Dp2') :-
                  translate (F Term) ET Dp1 (F' Term) ET' Dp1',
                  translate (exists F) (eSomeOrd Rest) Dp2 (exists F') (eSomeOrd Rest') Dp2'.

translate F eLit  F
          F eLit  F. % :- print "lit", term_to_string F Str, print Str.

% translate (exists x\ or (ng (r' x)) (r' (f x))) (eSome [(pr a' (eOr eLit eLit)), (pr (f a')  (eOr eLit eLit))]) Deep1 (exists x\ forall y\ or (ng (r' x)) (r' y)) T Deep2.

% translate (or (ng (r' a')) (r' (f a'))) (eOr eLit eLit)  (or Dp1 Dp2) (or A' B') (eOr eLit eLit) (or Dp1' Dp2').


test I :- skexample I (eC Exp) SkForm Form,
          translate SkForm Exp _ Form Exp' _,
          polarize Form B, check_exp (eC Exp') B.

% Tests for skolem trees
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
                   (pr (f a')  (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' (f x)))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with order
skexample 27 (eC
          (eSomeOrd [(pr a' (eOr eLit eLit)),
                     (pr (f a')  (eOr eLit eLit))]))
          (exists x\ or (ng (r' x)) (r' (f x)))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with inner skolemization
skexample 30 (eC
           (eSome [(pr a' (eOr eLit eLit)),
                   (pr a'  (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' a'))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

skexample 40 (eC
           (eOr (eSome [(pr b' (eSome [(pr a' (eAnd eLit eLit))]))])
                (eOr eLit eLit)))
           (or (exists x\ (exists y\ and (r' x) (ng (r' y))) )  (or (r' a') (ng (r' b'))))
           (or (exists x\ (exists y\ and (r' x) (ng (r' y))) )  (or (forall x\ r' x) (forall x\ ng (r' x))) ).

skexample 41 (eC
           (eOr (eSome [(pr a' (eAnd eLit eLit))])
                (eOr eLit (eSome [(pr (f' a') eLit)]))))
           (or (exists x\ (and (s' x (f' x)) (ng (r' (f' x)))) )  (or (s' a' (f' a')) (exists x\ r' x)) )
           (or (exists x\ (forall y\ and (s' x y) (ng (r' y))) )  (or (forall x\ forall y\ s' x y) (exists x\ r' x)) ).

%% Trying an example inspired by modal logic
%% Original formula
% (forall x\ forall y\ forall z\ (or  (and (ng (s' x y)) (ng (s' x z))) (exists w\ (and (s' y w) (s' z w)))))
% (forall x\ forall y\ forall z\ (or (or (ng (s' x y)) (ng (s' y z))) (s' x z) ))
% (and (s' a b) (and (s' b c) (and (s' c d) (s' a e))))
% (exists f\ (and (s' d f) (s' e f)))
% NNF
% (exists x\ exists y\ exists z\ (and  (or (s' x y) (s' x z)) (forall w\ (or (ng (s' y w)) (ng (s' z w))))))
% (exists x\ exists y\ exists z\ (and (and (s' x y) (s' y z)) (ng (s' x z)) ))
% (or (ng (s' a b)) (or (ng (s' b c)) (or (ng (s' c d)) (ng (s' a e)))))
% (exists f\ (and (s' d f) (s' e f)))


% (or (exists x\ exists y\ exists z\ (and  (or (s' x y) (s' x z))
%                                          (forall w\ (or (ng (s' y w)) (ng (s' z w))))))
%     (or (exists x\ exists y\ exists z\ (and (and (s' x y) (s' y z)) (ng (s' x z)) ))
%         (or (or (ng (s' a b))
%                 (or (ng (s' b c)) (or (ng (s' c d)) (ng (s' a e)))))
%             (exists f\ (and (s' d f) (s' e f))))))

% (eOr (eSome [(pr TERM_X1 (eSome [(pr TERM_Y1 (eSome [(pr TERM_Z1 (eAnd (eOr eLit eLit)
%                                                                  (eAll w (eOr eLit eLit)) ))]))] ))])
%      (eOr (eSome [(pr TERM_X1 (eSome [(pr TERM_Y1 (eSome [(pr TERM_Z1 (eAnd (eAnd eLit eLit) eLit))]))]))])
%           (eOr (eOr eLit
%                     (eOr eLit (eOr eLit eLit)))
%                 )


% Double drinker formula, as suggested by J Urban
example 99
(eIntro x1\ eIntro x2\ eIntro z1\ eIntro z2\ eC
          (eSome [(pr a' (eSome [(pr b' (eAll x1 (eAll z1 (eOr (eOr eLit eLit) (eOr eLit eLit))))),
                                 (pr z1 (eAll x1 (eAll z2 (eOr (eOr eLit eLit) (eOr eLit eLit)))))])),
                  (pr x1 (eSome [(pr b' (eAll x2 (eAll z1 (eOr (eOr eLit eLit) (eOr eLit eLit))))),
                                 (pr z1 (eAll x2 (eAll z2 (eOr (eOr eLit eLit) (eOr eLit eLit)))))]))]))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (q z)) (q w)))).

% Double drinker formula as Skolem-example
skexample 98
(eC
       (eSome [(pr a' (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                              (pr (h' a' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))])),
          (pr (g a' b') (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                             (pr (h' a' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))]))]))
(exists y\ exists w\ (or (or (ng (r' (g y w))) (r' y)) (or (ng (q (h' y w))) (q w))))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (q z)) (q w)))).


% Double drinker formula as Skolem-example with inner skolem
skexample 100
(eC
       (eSome [(pr a' (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                              (pr (f' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))])),
          (pr (f a') (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                             (pr (f' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))]))]))
(exists y\ exists w\ (or (or (ng (r' (f y))) (r' y)) (or (ng (q (f' w))) (q w))))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (q z)) (q w)))).


% skexample 21
% (and (forall x\  forall y\ ng (p x y))  (forall u\ exists v\ (or (p u v) (p u v))))
% (and (forall x\  forall y\ ng (p x y))  (forall u\ exists v\ (or (p u v) (p u v))))

% S : ∀x ∀y ¬P(x,y), ∀u ∃v (P(u,v) ∨ P(u,v)) |-
% S1: ∀x ∀y ¬P(x,y), ∀u (∃v P(u,v) ∨ ∃v P(u,v)) |-

% Skolemized:
% S' : ∀x ∀y ¬P(x,y), ∀u (P(u,f(u)) ∨ P(u,f(u))) |-
% S1': ∀x ∀y ¬P(x,y), ∀u (P(u,f(u)) ∨ P(u,g(u))) |-

