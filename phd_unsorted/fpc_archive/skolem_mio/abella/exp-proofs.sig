sig exp-proofs.

kind form, i,bool, atm                    type. % Formulas, terms, and atoms
kind et       type.  % expansion trees
kind pair     type.
type pr       i -> et -> pair.

kind list type.
type null list.
type cons pair -> list -> list.

kind et       type.  % expansion trees
kind qet      type.  % quantified expansion trees (leading introduction of select vars)

type tt, ff                     bool.
type ng                     	bool -> bool.
type and, or, imp, equiv    	bool -> bool -> bool.
type all, ex             (i -> bool) -> bool.

%infixr e-e, e+e  6.
%infixr o-o, o+o  5.

type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos        form -> o. 
type negate                                                form -> form -> o.


% Notice that the definition of ensure satisfies the 
% deMorgan principles:
%  |- ensure+ A B, negate B C   holds if and only if
%  |- negate A D, ensure- D C
type ensure-, ensure+     form -> form -> o.


%typeabbrev subExp    list (pair i et).    % Expansions for a node

type eIntro            (i -> qet) -> qet.
type eC                et -> qet.

type eTrue, eFalse     et.
type eLit              et.
type eAnd, eOr	       et -> et -> et.
type eAll              i  -> et -> et.	
type eSome             list    -> et.
type eSomeOrd          list    -> et.

type translate bool -> et -> bool -> bool -> et -> bool -> o.