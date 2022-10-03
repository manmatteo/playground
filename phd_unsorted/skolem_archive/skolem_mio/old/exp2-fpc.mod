/* Notes: 

   Revising previous exp-fpc file.

   The Left component in the astate and sstate certificates
   should probably be split into two parts: one containing just
   literals and one containing just existentials.  This would help
   make the code cleaner and a bit faster.
*/

module exp2-fpc.

% Used to translate "client" terms to "kernel" terms: in expansion
% trees, we have selection variables while in the kernel we have
% eigenvariables.  The first argument of translate_term is an
% association list between these two kind of items.

translate_term []             Term Term' :- copy Term Term'.
translate_term ((pr X Y)::As) Term Term' :- copy X Y => translate_term As Term Term'.

% The all-clerk adds a pair to this association list.

allC   (   astate               Vs  Lits Exs ((pr ForallB (eAll Uvar E))::Qs))
       (x\ astate ((pr Uvar x)::Vs) Lits Exs ((pr (B x)              E) ::Qs)) :- all- B ForallB.


% After instantiating the existential, we are followed by a delay-.
% Thus, we introduce a new certificate constructor to guide us
% through this small detour.
someE (sstate Vs Lits Exs Form (eSome [pr Term ExTree]))
      (dstate Vs Lits Exs [(pr (Body Term') ExTree)])    Term' :-
  some+ Body Form, translate_term Vs Term Term'.

orC    (astate Vs Lits Exs ((pr B (eOr E1 E2))::Qs))
       (astate Vs Lits Exs ((pr B1 E1)::(pr B2 E2)::Qs))         :- disj- B1 B2 B.
andC   (astate Vs Lits Exs ((pr B (eAnd E1 E2))::Qs))
       (astate Vs Lits Exs ((pr B1 E1)::Qs))
       (astate Vs Lits Exs ((pr B2 E2)::Qs))                     :- conj- B1 B2 B.
falseC (astate Vs Lits Exs ((pr B eFalse)::Qs))
       (astate Vs Lits Exs Qs)                                   :- false- B.

storeC (astate Vs Lits         Exs ((pr Form eLit)::Qs))
       (astate Vs (Form::Lits) Exs                  Qs)
       (idx Form)                          :- lit- _ Form; lit+ _ Form.
storeC (astate Vs Lits                Exs ((pr Form ET)::Qs))
       (astate Vs Lits ((pr Form ET)::Exs)               Qs)
       (idx Form)                          :- some+ _ Form.

decideE (astate Vs Lits Exs []) (sstate Vs Lits Exs Plit eLit) (idx Plit) :- 
 % Decide on a literal only if no existentials are present
  foreach (pair\ sigma Lit\ pair = (pr Lit eLit)) Left,
  memb (pr Plit eLit) Left.

decideE
  (astate Vs Lits Exs [])
  (sstate Vs Left' Exists (eSome [pr Term ExTree]))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSome [pr Term ExTree])) Lits Exs Left'.

decideE
  (astate Vs Lits Exs [])
  (sstate Vs Lits ((pr Exists (eSome SubExp'))::Exs') Exists (eSome [pr Term ExTree]))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSome SubExp)) Exs Exs',
  memb_and_rest (pr Term ExTree) SubExp SubExp', SubExp' = (_::_).

decideE
  (astate Vs Lits Exs [])
  (sstate Vs Lits Exs' Exists (eSome [pr Term ExTree]))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSomeOrd [pr Term ExTree])) Exs Exs'.

decideE
  (astate Vs Lits Exs [])
  (sstate Vs Lits ((pr Exists (eSomeOrd SubExp'))::Exs') Exists (eSome [pr Term ExTree]))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSomeOrd SubExp)) Exs Exs',
  SubExp = ((pr Term ExTree)::SubExp'), SubExp' = (_::_).

releaseE (sstate Vs Lits Exs Form Exp) (astate Vs Lits Exs [(pr Form Exp)]).

initialE _ _.
trueE    _.

releaseE (dstate Vs Lits Exs Neg) (dstate Vs Lits Exs Neg).
orC      (dstate Vs Lits Exs ((pr B E)::nil))
         (dstate Vs Lits Exs ((pr B1 eFalse)::(pr B2 E)::nil)) :- disj- B1 B2 B.
falseC   (dstate Vs Lits Exs ((pr B eFalse)::(pr B2 E2)::nil))
         (astate Vs Lits Exs ((pr B2 E2)::nil))                :- false- B.
