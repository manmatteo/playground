/*
9 apr 18 (MM)
Port of the original exp-fpc for Expansion tree, to use the new mechanism for
handling kernel-side and client-side formulas instead of the old translation
done inside the FPC. This also allows to directly check a proof tree for a
skolemized formula as proof evidence for the original formula.

Original notes follow
%%%

 Notes: There is a lot of non-determinism in the selection of an
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
 longer remembered
*/
module exp-sk-fpc.

orC    (astate Left ((pr B (eOr E1 E2))::Qs))
       (astate Left ((pr B1 E1)::(pr B2 E2)::Qs))         :- disj- B1 B2 B.
andC   (astate Left ((pr B (eAnd E1 E2))::Qs))
       (astate Left ((pr B1 E1)::Qs))
       (astate Left ((pr B2 E2)::Qs))                     :- conj- B1 B2 B.

% The expansion tree contains a select variable in correspondence with a universal
% quantifier: use that select variable to name the eigenvariable in the kernel
allCxx  (astate Left ((pr ForallB (eAll Uvar E))::Qs))
        (w\ astate Left ((pr (B w) E)::Qs)) Uvar :- all- B ForallB.
% The expansion tree does not contain a select variable at a universal quantifier:
% introduce a logic variable representing a Skolem term that will be figured out
% later, and use it as a name for the eigenvariable

% DM There is an overlap between the clause above and the next one.  I remove using a not =.

allCxx  (astate Left ((pr ForallB E)::Qs))
        (w\ astate Left ((pr (B w) E)::Qs)) Sk :- all- B ForallB, not (E = (eAll _ _)).

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
% someE (sstate Left (pr Form (eSome [pr Term ExTree])))
%       (dstate Left [(pr (Body Term') ExTree)])
%       Term' :-
%   some+ Body Form, ck_translate Term Term'.

someE (sstate Left (pr Form (eSome [pr Term ExTree])))
      (dstate Left [(pr (Body Term) ExTree)])
      Term :-
  some+ Body Form.

releaseE (sstate Left Neg) (astate Left [Neg]).

initialE _ _.

trueE _.

releaseE (dstate Left Neg) (dstate Left Neg).
% RB: B disappears here disappears as external formula, and (pr D E) becomes
% (pr B E).
orC      (dstate Left ((pr B E)::nil))
         (dstate Left ((pr B1 eFalse)::(pr B2 E)::nil)) :- disj- B1 B2 B.
falseC   (dstate Left ((pr B eFalse)::(pr B2 E2)::nil))
         (astate Left ((pr B2 E2)::nil))                :- false- B.
