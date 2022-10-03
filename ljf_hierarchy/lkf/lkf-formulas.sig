% Kernal side formula, also known as polarized formulas.

% Client-side terms and atomic formulas are embedded into this client-side formulas. 
%   Client-side terms have type i
%   Client-side atomic formulas can have any type (via polymorphic type of p and n)

sig lkf-formulas.

kind form, i                         type. % Formulas and terms

type n, p                       A -> form. % Constructors of literals
type f+, f-, t+, t-                  form. % Units
type d-, d+                  form -> form. % Delays 
type &-&, &+&        form -> form -> form. % Conjunctions
type !-!, !+!        form -> form -> form. % Disjunction
type all, some       (i -> form)  -> form. % Quantifiers

infixr &-&, &+&  6.
infixr !-!, !+!  5.

type isNegForm, isNegAtm, isNeg        form -> o. 
type isPosForm, isPosAtm, isPos        form -> o. 

type negate                    form -> form -> o.
type ensure+, ensure-          form -> form -> o.
