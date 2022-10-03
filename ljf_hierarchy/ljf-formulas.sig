% Kernal side formula, also known as polarized formulas.

% Client-side terms and atomic formulas are embedded into this client-side formulas. 
%   Client-side terms have type i
%   Client-side atomic formulas can have any type (via polymorphic type of p and n)

sig ljf-formulas.

kind form, i                     type. % Formulas and terms

type n, p           A -> form.         % Constructors of literals
type d-, d+      form -> form.         % Delays 
type and-, and+  form -> form -> form. % Conjunctions
type or+         form -> form -> form. % Disjunction
type arr         form -> form -> form. % Implication
type all, some   (i -> form)  -> form. % Quantifiers
type f, t+, t-                   form. % Units

infixr and-, and+ 6.
infixr or+  5.
infixr arr 4.


type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos     form -> prop. 
