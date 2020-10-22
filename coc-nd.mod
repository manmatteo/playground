module coc-nd.
axiom p t.
rel p p p. rel p t t. rel t p p. rel t t t.

% async A B :- print "async" A B, fail.
% astr A B :- print "astr" A B, fail.
% sync A B C :- print "sync" A B C, fail.

of (sort X) (sort Y) :-
  axiom X T.

of T A :-
  of A (sort S).

of (prod A B) (sort S3) :-
  of A (sort S1),
  pi w\ of w A => of (B w) (sort S2).
  rel S1 S2 S3.

of (app (C :: T :: nil)) (B T) :-
  of C (prod A B),
  of T A. 

of (fun A T) (prod A B) :-
  of (prod A B) (sort _),
  pi w\ of w A =>
    of (T w) (B w).

of A B :-
  of B (sort _),
  beta B B',
  of A B'.

beta (app (fun Ty T :: Tm :: nil)) (T Tm).
