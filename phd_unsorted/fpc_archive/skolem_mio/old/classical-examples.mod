module classical-examples.

example 1 (or q (ng q)).
example 2 (equiv (equiv m q) (equiv q m)).
example 3 (equiv (imp q m) (imp (ng m) (ng q))).
example 4 (equiv (equiv q m) (equiv (ng m) (ng q))).
example 5 (imp (imp (imp q m) q) q).
example 6 (imp (equiv q m) (equiv m q)).
example 7 (imp (equiv q m) (equiv (ng m) (ng q))).
example 8 (equiv q q).
example 9 (imp (imp q m) (imp q m)).
example 10 (imp (and m q) (and m q)).
example 11 (imp (and q m) m).
% The following are examples 8, 12, 17 (resp) from 
% Pelletier's article "Seventy-Five Problems for testing Atomatic
% theorem Provers" (JAR 1986).
example 12 (imp (imp (imp q m) q) q). 
example 13 (equiv (equiv (equiv mm m) q) (equiv mm (equiv m q))).
example 14 (equiv (imp (and mm (imp m q)) qq)
                  (and (or (ng mm) (or m qq))
                       (or (ng mm) (or (ng q) qq)))).
example 15 (imp q (and q q)).

%/*  Not tautologies
%example 20 ((b equiv a) equiv ((ng c) equiv (ng b))). 
%example 21 (b equiv a).
%example 22 ((b equiv a) equiv (d equiv c)).
%example 23 (Ex4 and c) :- example 4 Ex4.
%*/

% The following example is credited to Quine in "First-order logic" by Smullyan
% This can be proved using decide depth 3.
% ?- example 30 F, polarize F G, lkf_entry (dd (s (s (s zero)))) G.

% example 30 
%   (imp (imp (forall x\ (imp (and (f x) (g x)) (h x))) (exists x\ (and (f x) (ng (g x)))))
%   (imp (or (forall x\ imp (f x) (g x)) (forall x\ imp (f x) (h x)))
%   (imp (forall x\ imp (and (f x) (h x)) (g x))
%       (exists x\ (and (f x) (and (g x) (ng (h x)))))))).

% Examples 31, 32, 33 are related: assume that the binary relation is
% transitive and has has the "local diamond property".  Then show that
% bigger diamonds exist.

example 31
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r y z) (r x z))))
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r x z) (exists w\ (and (r y w) (r z w))))))
  (imp (r n1 n2) 
  (imp (r n1 n5)
  (exists u\ (and (r n2 u) (r n5 u))))))).

example 32
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r y z) (r x z))))
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r x z) (exists w\ (and (r y w) (r z w))))))
  (imp (r n1 n2) 
  (imp (r n2 n3)
  (imp (r n1 n5)
  (exists u\ (and (r n3 u) (r n5 u)))))))).

example 33
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r y z) (r x z))))
  (imp (forall x\ forall y\ forall z\ (imp (r x  y) (imp (r x z) (exists w\ (and (r y w) (r z w))))))
  (imp (r n1 n2) 
  (imp (r n2 n3)
  (imp (r n3 n4)
  (imp (r n1 n5)
  (exists u\ (and (r n4 u) (r n5 u))))))))).

