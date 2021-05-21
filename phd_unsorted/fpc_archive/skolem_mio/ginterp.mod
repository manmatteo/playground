% Proof certificates for forward chaining with geometric theories

module ginterp.
accumulate lib.
accumulate classical.

% async A B C D :- announce (async A B C D).
% syncL A B C D :- announce (syncL A B C D).
% syncR A B     :- announce (syncR A B).
skolemized A B  :- announce (skolemized A B).
sk_positive A B :- announce (sk_positive A B).


positive (and P Q) & positive (or  P Q) :- positive P, positive Q.
positive (exists P)                     :- pi x\ positive (P x).
positive A                              :- atomic A.

% Geometric clauses are the following. (This might be generalized a bit.)
gclause (forall C) :- pi x\ gclause (C x).
gclause (imp A C)  :- atomic A, gclause C.
gclause C          :- positive C.

% The only sequents considered for proof checking are of the form
%  async:    Theory, Atoms, Goal  :- Atom
%   syncL:   Theory, Atoms | Clause :- Atom+
%   syncR:   Theory, Atoms :- Goal

async Atoms [(or G1 G2)|Delta] Goal Cert :- async Atoms [G1|Delta] Goal Cert; async Atoms [G2|Delta] Goal Cert.
async Atoms [(and G1 G2)|Delta] Goal Cert:- async Atoms [G1,G2|Delta] Goal Cert.
async Atoms [(exists G)|Delta] Goal (evar Cert) :- pi x\ async Atoms [(G x)|Delta] Goal (Cert x).
async Atoms [A|Delta] Goal Cert :- atomic A, async [A|Atoms] Delta Goal Cert.
async Atoms [] Atom (decide Index Cert) :- theory Index Clause, syncL Atoms Clause Atom Cert.
async Atoms [] Goal done :- syncR Atoms Goal.

syncR Atoms (exists G)  :- syncR Atoms (G T).
syncR Atoms (and G1 G2) :- syncR Atoms G1, syncR Atoms G2.
syncR Atoms (or  G1 G2) :- syncR Atoms G1; syncR Atoms G2.
syncR Atoms Atom        :- atomic Atom, memb Atom Atoms.

syncL Atoms (forall Clause) Atom (inst T Cert) :- syncL Atoms (Clause T) Atom Cert.
syncL Atoms (imp A D) Atom Cert  :- memb A Atoms, syncL Atoms D Atom Cert.
syncL Atoms Pos Atom Cert        :- positive Pos, async Atoms [Pos] Atom Cert.

% theory index Geometric

theory ref        (forall x\ r x x).
theory sym        (forall x\ forall y\ imp (r x y) (r y x)).
theory trans      (forall x\ forall y\ forall z\ imp (r x y) (imp (r y z) (r x z))).
theory euclidean  (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (r y z))).
theory connected  (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (or (r y z) (r z y)))).
theory serial     (forall x\ exists y\ r x y).
theory directed   (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (exists w\ and (r y w) (r z w)))).
theory sk1serial   (forall x\ r x (sk1 x)).
       % Using inner skolemization 
theory sk2directed (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (and (r y (sk2 y z))   (r z (sk2 y z))))).
       % Using outer skolemization 
theory sk3directed (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (and (r y (sk3 x y z)) (r z (sk3 x y z))))).

test I :- gexample I Atoms Goal Cert, async Atoms [] Goal Cert.

gexample 1 [(r a b),(r a c)]
           (exists X\ and (r b X) (r c X))
	   (decide directed (inst a (inst b (inst c (evar x\ done))))).

gexample 2 [(r a b),(r b c),(r a e)]
           (exists X\ and (r e X) (r c X))
           (decide directed (inst a (inst b (inst e (evar x\
	    decide directed (inst b (inst c (inst x (evar y\
	    decide trans    (inst e (inst x (inst y
	    done)))))))))))).

gexample 3 [] (r a a)
           (decide serial (inst a (evar x\
           (decide sym    (inst a (inst x
	   (decide trans  (inst a (inst x (inst a done)))))))))).

gexample 4 [] (r a a)
           (decide sk1serial (inst a 
           (decide sym       (inst a (inst (sk1 a)
	   (decide trans     (inst a (inst (sk1 a) (inst a done))))))))).

gexample 5 [(r a b),(r b c),(r a e)]
           (exists X\ and (r e X) (r c X))
           (decide sk2directed (inst a (inst b (inst e 
	   (decide sk2directed (inst b (inst c (inst (sk2 b e) 
	   (decide trans    (inst e (inst (sk2 b e) (inst (sk2 c (sk2 b e))
	    done)))))))))))).

gexample 6 [(r a b),(r b c),(r a e)]
           (exists X\ and (r e X) (r c X))
           (decide sk3directed (inst a (inst b (inst e 
	   (decide sk3directed (inst b (inst c (inst (sk3 a b e) 
	   (decide trans    (inst e (inst (sk3 a b e) (inst (sk3 b c (sk3 a b e))
	    done)))))))))))).

gexample 7 [] (exists x\ exists y\ exists z\ and (r a x) (and (r x y) (r y z)))
           (decide serial (inst a (evar w\
           (decide serial (inst w (evar v\ 
           (decide serial (inst v (evar u\
           done))))))))).

gexample 8 [] (exists x\ exists y\ exists z\ and (r a x) (and (r x y) (r y z)))
           (decide sk1serial (inst a 
           (decide sk1serial (inst (sk1 a) 
           (decide sk1serial (inst (sk1 (sk1 a)) 
           done)))))).

skolemized (forall C) (forall K) :- pi x\ copyi x x => skolemized (C x) (K x).
skolemized (imp A C)  (imp A' K) :- copybool A A', skolemized C K.
skolemized C K                   :- sk_positive C K.

sk_positive (and P Q) (and K H) &
sk_positive (or  P Q) (and K H) :- sk_positive P K, sk_positive Q H.
sk_positive (exists P) Q        :- pi x\ copyi x T => sk_positive (P x) Q.
sk_positive A A'                :- spy(copybool A A').
