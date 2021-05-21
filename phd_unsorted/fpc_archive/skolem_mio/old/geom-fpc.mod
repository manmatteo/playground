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
storeC (astate Vs Context List)
       (astate Vs ((pr Form (N+1)) :: Context) List)
       (idx (N+1)) :- some+ _ Form, length Context N.

orC    (astate Vs Context List)
       (astate Vs Context List)                   :- disj- B1 B2 B.
andC   (astate Vs Context List)
       (astate Vs Context List)
       (astate Vs Context List)                   :- conj- B1 B2 B.
allC   (astate Vs Context List)
       (x\ astate Vs Context List) :- all- B ForallB.
falseC (astate Vs Context List)
       (astate Vs Context List)                   :- false- B.

% We should only be storing atoms when we are not in istate, so no need to remember them
storeC (astate Vs Context List)
       (astate Vs Context List)
       (idx N)                          :- lit- _ Form; lit+ _ Form.
% storeC (astate Vs Context ((pr Form ET)::Qs))
%        (astate Vs ((pr Form ET)::Context) Qs)
%        (idx Form)                          :- some+ _ Form.

% decideE (astate Vs [] []) (sstate Vs [] (pr Plit eLit)) (idx Plit). 
% Decide on a literal only if no existentials are present
decideE
  (astate Vs Context (N::List))
  (sstate Vs Context List)
  (idx N) :-
  memb (pr Form N) Context.

someE (sstate Vs Context List)
      (sstate Vs Context List)
      Term' :-
  memb (pr Form _) Context,
  some+ _ Form. %, translate_term Vs Term Term'.

releaseE (sstate Vs Context List) (astate Vs Context List).

initialE _ _.
trueE _.