/* 
A small fpc to easily certify proofs of geometrical formulas
*/
module geom-fpc.

% with the different treatment of eigenvariables in expansion trees
% and in sequent calculus.

translate_term [] Term Term' :- copy Term Term'.
translate_term ((pr X Y)::As) Term Term' :- copy X Y => translate_term As Term Term'.

% Initial preprocessing
% orC    (astate Vs Context List)
%        (astate Vs Context List)     :- disj- B1 B2 B.

% storeC (astate Vs Context [])
%        (astate Vs ((pr B1 N) :: Context) List)
%        (idx N).

% We want to store the existential (i.e. negated universal) axioms
% storeC (astate Vs Cert)
%        (astate Vs ((pr Form (N+1)) :: Context) List)
%        (idx (N+1)) :- some+ _ Form.

orC    (astate Vs Cert)
       (astate Vs Cert)                   :- disj- B1 B2 B.
andC   (astate Vs Cert)
       (astate Vs Cert)
       (astate Vs Cert)                   :- conj- B1 B2 B.
allC   (astate Vs Cert)
       (x\ astate Vs Cert)                :- all- B ForallB.
falseC (astate Vs Cert)
       (astate Vs Cert)                   :- false- B.

% We should only be storing atoms when we are not in istate, so no need to remember them
storeC (astate Vs Cert)
       (astate Vs Cert)
       (idx N)                          :- lit- _ Form; lit+ _ Form.
% storeC (astate Vs Context ((pr Form ET)::Qs))
%        (astate Vs ((pr Form ET)::Context) Qs)
%        (idx Form)                          :- some+ _ Form.

% decideE (astate Vs [] []) (sstate Vs [] (pr Plit eLit)) (idx Plit). 
% Decide on a literal only if no existentials are present
decideE
  (astate Vs Context (decide Index Cert))
  (sstate Vs Cert)
  (idx N) :-
  memb (pr Form N) Context.

someE (sstate Vs Cert)
      (sstate Vs Cert)
      Term' :-
  memb (pr Form _) Context,
  some+ _ Form. %, translate_term Vs Term Term'.

releaseE (sstate Vs Cert) (astate Vs Cert).

initialE _ _.
trueE _.


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