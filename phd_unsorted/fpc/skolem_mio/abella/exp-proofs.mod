module exp-proofs.

translate F Q Dp
          (all A) (eAll T Q') Dp' :- translate F Q Dp (A T) Q' Dp'.
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

translate (ex F) (eSome (cons (pr Term ET) null)) Dp
          (ex F') (eSome (cons (pr Term ET') null)) Dp' :-
                                 translate (F Term) ET Dp (F' Term) ET' Dp',
                                 translate (F Term) ET Dp (F' Term) ET' Dp'.

translate (ex F) (eSome (cons (pr Term ET) Rest)) (or Dp1 Dp2)
          (ex F') (eSome (cons (pr Term ET') Rest')) (or Dp1' Dp2') :-
                  translate (F Term) ET Dp1 (F' Term) ET' Dp1',
                  translate (ex F) (eSome Rest) Dp2 (ex F') (eSome Rest') Dp2'.

translate F eLit  F
          F eLit  F. % :- print "lit", term_to_string F Str, print Str.
