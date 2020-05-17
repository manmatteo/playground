/* Notes: There is a lot of non-determinism in the selection of an
   expansion term when one views the collection of expansion terms
   used to instantiate a quantifier as being a multiset.  This
   observation leads to at least three ways to present the expansion
   terms associated to an existential quantifier.

   (1) as a multiset
   (2) as a list (take the multiset in 1 and do a topological sort 
       using the dependency relation) 
   (3) as a list of multisets of element (take the dependency relation,
       and repeated collect together the minimal elements.  Notice that
       the multisets here can also be lists (the order there, however,
       is arbitrary.

 Notes: The Left component in the astate and sstate certificates
 should probably be split into two parts: one containing just
 literals and one containing just existentials.  This would help
 make the code cleaner and a bit faster.
 UPDATE: MM 19/01/18: Left only stores existentials, literals are no 
 longer remembered (line 42)
*/
module exp_sk-fpc.

accumulate ck-trans.
% Used to translate "external" terms to "internal" terms (has to do
% with the different treatment of eigenvariables in expansion trees
% and in sequent calculus.

%translate_term [] Term Term' :- copyi Term Term'.
%translate_term ((pr X Y)::As) Term Term' :- copyi X Y => translate_term As Term Term'.

orC    (astate Left ((pr B (eOr E1 E2))::Qs))
       (astate Left ((pr B1 E1)::(pr B2 E2)::Qs))         :- disj- B1 B2 B.
andC   (astate Left ((pr B (eAnd E1 E2))::Qs))
       (astate Left ((pr B1 E1)::Qs))
       (astate Left ((pr B2 E2)::Qs))                     :- conj- B1 B2 B.
% allC   (astate Vs Left ((pr ForallB (eAll Uvar E))::Qs))
%        (x\ astate ((pr Uvar x)::Vs) Left ((pr (B x) E)::Qs)) :- all- B ForallB.
% allCx (asyn Cert) (w\ asyn Cert) (w\ localcp Sk w).
allCx   (astate Left ((pr ForallB (eAll Uvar E))::Qs))
       (w\ astate Left ((pr (B w) E)::Qs)) (w\ localcp Uvar w) :- all- B ForallB.
allCx   (astate Left ((pr ForallB E)::Qs))
       (w\ astate Left ((pr (B w) E)::Qs)) (w\ localcp Sk w):- all- B ForallB.
falseC (astate Left ((pr B eFalse)::Qs))
       (astate Left Qs)                                   :- false- B.

% RB: Removing Form as inspecting formula.
% MM: Don't record literals
storeC (astate Left ((pr Form ET)::Qs))
       (astate Left Qs)
       (idx Form)                          :- lit- _ Form; lit+ _ Form.
storeC (astate Left ((pr Form ET)::Qs))
       (astate ((pr Form ET)::Left) Qs)
       (idx Form)                          :- some+ _ Form.

% RB: From mdecide to decide.
% MM: Check no longer needed: decide on literals only when Left is empty
decideE (astate [] []) (sstate [] (pr Plit eLit)) (idx Plit). 
 % % Decide on a literal only if no existentials are present
 %  foreach (pair\ sigma Lit\ pair = (pr Lit eLit)) Left,
 %  memb (pr Plit eLit) Left.

decideE
  (astate Left [])
  (sstate Left' (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSome [pr Term ExTree])) Left Left'.

decideE
  (astate Left [])
  (sstate   ((pr Exists (eSome SubExp'))::Left') (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSome SubExp)) Left Left',
  memb_and_rest (pr Term ExTree) SubExp SubExp', SubExp' = (_::_).

decideE
  (astate Left [])
  (sstate Left' (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSomeOrd [pr Term ExTree])) Left Left'.

decideE
  (astate Left [])
  (sstate ((pr Exists (eSomeOrd SubExp'))::Left') (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSomeOrd SubExp)) Left Left',
  SubExp = ((pr Term ExTree)::SubExp'), SubExp' = (_::_).

% After instantiating the existential, we are followed by a delay-.
% Thus, we introduce a new certificate constructor to guide us
% through this small detour.
someE (sstate Left (pr Form (eSome [pr Term ExTree])))
      (dstate Left [(pr (Body Term') ExTree)])
      Term' :-
  some+ Body Form, ck_translate Term Term'.

releaseE (sstate Left Neg) (astate Left [Neg]).

initialE _ _.% X Y :- term_to_string X Str1, term_to_string Y Str2, print Str1, print Str2.

trueE _.

releaseE (dstate Left Neg) (dstate Left Neg).
% RB: B disappears here disappears as external formula, and (pr D E) becomes
% (pr B E).
orC      (dstate Left ((pr B E)::nil))
         (dstate Left ((pr B1 eFalse)::(pr B2 E)::nil)) :- disj- B1 B2 B.
falseC   (dstate Left ((pr B eFalse)::(pr B2 E2)::nil))
         (astate Left ((pr B2 E2)::nil))                :- false- B.
