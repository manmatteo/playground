atom (mu B). % :- pi x\ form x => atom (B x).
atom (nu B). % :- pi x\ form x => atom (B x).
atom one.

bot (nu B) (mu B).
bot (mu B) (nu B).
bot (with A B)  (sum A1 B1)  :- bot A A1, bot B B1.
bot (sum A B)   (with A1 B1) :- bot A A1, bot B B1.
bot (par A B)   (times A1 B1):- bot A A1, bot B B1.
bot (times A B) (par A1 B1)  :- bot A A1, bot B B1.

form P :- atom P.
form (with A B)  :- form A, form B.
form (sum A B)   :- form A, form B.
form (par A B)   :- form A, form B.
form (times A B) :- form A, form B.

linctx nil.
linctx (X::G) :- form X, linctx G.
inctx E (E::C) C :- linctx C.
inctx E (_::C) R :- inctx E C R.
% splitctx nil C C.
% splitctx C nil C.
splitctx nil nil nil.
splitctx C nil C.
splitctx nil C C.
splitctx C1 C2 (H::T) :- inctx H C1 R, splitctx R C2 T.
splitctx C1 C2 (H::T) :- inctx H C2 R, splitctx C1 R T.

of G (case X) (par A B) :- linctx G, of (cons A G) X B.
of G (case X) (par A B) :- linctx G, of (cons B G) X A.
of G (inj1 X) (sum A B) :- linctx G, of G X A.
of G (inj2 X) (sum A B) :- linctx G, of G X B.
of G (lazypair X Y) (with A B):- of G X A, of G Y B.
of G (pair X Y) (times A B):- splitctx G1 G2 G, of G1 X A, of G2 Y B.
of G (corec X Y) (nu B)    :- form S, of G X S, bot S S1, of (B S) Y S1.
of G (unfold X) (mu B)    :- of G X (B (mu B)).
of (mu B) (init) (nu B).
of nil (true) one.

ty nat (mu p\ sum one p).
tm three (unfold (inj2 (unfold (inj2 (unfold (inj1 true)))))).

