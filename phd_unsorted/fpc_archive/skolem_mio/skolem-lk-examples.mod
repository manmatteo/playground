module skolem-lk-examples.
accumulate maxcert.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate lkf-kernel.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Examples with skolemized formulas with the maxcert FPC (ie fully explicit LKF)

% NOTE: Terms are sometimes a,b,f,g... and sometimes sk1, sk1f...
% The first set is in the common signature. The second in the Skolem
% signature. This is used in order to check skolemized proofs against
% skolemizd formulas, or skolemized proofs against non skolemized formulas.

% Predicates and funcitons in the signature are declared in classical.mod
% Skolem symbols are included in the signature of this file

% Simple example to understand how things are written
example 1
(max 1
(max1 % or-
(maxi (ix 1) % store q
(maxi (ix 2) % store (ng q)
(maxi (ix 1) % decide q
(maxa (ix 2) % init (ng q)
))))))
(or q (ng q)).


% The base case formula from Baaz et al. JSL2012, with a delay added
% by using the vacuous existential (exists u) This is a proof of the
% inner skolemization, against the skolemized formula
example 2
(max 1
(max1 % or-
(maxi (ix 1) % store (exists (u\ (and ...)))
(maxi (ix 2) % store (exists (y\ (or ...)))
(maxi (ix 1) % decide (exists (u\ (and ...)))
(maxt a % exist (NB dummy existential, here as a delay)
(max1 % release
(max2 % and-
  (maxi (ix 3) % store (ng (s a))
  (maxi (ix 2) % decide (exists (y\ (or ...)))
  (maxt a % exist
  (max1 % release
  (max1 % or-
  (maxi (ix 4) % store (s a)
  (maxi (ix 5) % store (ng q)
  (maxi (ix 4) % decide (s a)
  (maxa (ix 3) % init (ng (s a))
  )))))))))
  (maxi (ix 3) % store (ng q)
  (maxi (ix 2) % decide (exists (y\ (or ...)))
  (maxt a % exist
  (max1 % release
  (max1 % or-
  (maxi (ix 4) % store (s a)
  (maxi (ix 5) % store q
  (maxi (ix 5) % decide q
  (maxa (ix 3) % init (ng q)
  )))))))))
))))))))
(or (exists (u\ (and (ng (s a))  (ng q))))
    (exists (y\ (or  (s y)  q)))).

% The same proof, but against the original formula.
% It checks! Indeed this same proof also works with outer skolemization
example 3
(max 1(max1 (maxi (ix 1) (maxi (ix 2) (maxi (ix 1)
(maxt a % dummy
(max1 (max2 (maxi (ix 3) (maxi (ix 2)
(maxt sk1
(max1 (max1 (maxi (ix 4) (maxi (ix 5) (maxi (ix 4) (maxa (ix 3) ))))))))) (maxi (ix 3) (maxi (ix 2)
(maxt sk1
(max1 (max1 (maxi (ix 4) (maxi (ix 5) (maxi (ix 5) (maxa (ix 3) )))))))))))))))))
(or (exists (u\ forall (x\ (and (ng (s x)) (ng q)))))
    (exists (y\ (or  (s y)  q)))).

% The initial example, with outer skolemization, checked against the
% skolemized formula.
example 4
(max 1
(max1 % or-
(maxi (ix 1) % store (exists (u\ (and ...)))
(maxi (ix 2) % store (exists (y\ (or ...)))
(maxi (ix 1) % decide (exists (u\ (and ...)))
(maxt a % exist (NB dummy existential, here as a delay)
(max1 % release
(max2 % and-
  (maxi (ix 3) % store (ng (s (f a)))
  (maxi (ix 2) % decide (exists (y\ (or ...)))
  (maxt (f a) % exist
  (max1 % release
  (max1 % or-
  (maxi (ix 4) % store (s (f a))
  (maxi (ix 5) % store (ng q)
  (maxi (ix 4) % decide (s (f a))
  (maxa (ix 3) % init (ng (s (f a)))
  )))))))))
  (maxi (ix 3) % store (ng q)
  (maxi (ix 2) % decide (exists (y\ (or ...)))
  (maxt a % exist
  (max1 % release
  (max1 % or-
  (maxi (ix 4) % store (s a)
  (maxi (ix 5) % store q
  (maxi (ix 5) % decide q
  (maxa (ix 3) % init (ng q)
  )))))))))
))))))))
(or (exists (u\ (and (ng (s (f u)))  (ng q))))
    (exists (y\ (or  (s y)  q)))).

% The initial example, with outer skolemization, checked against the
% original formula.
% Same certificate as example 4, but the skolem function f is now skf1
example 5
(max 1
(max1 % or-
(maxi (ix 1) % store (exists (u\ (and ...)))
(maxi (ix 2) % store (exists (y\ (or ...)))
(maxi (ix 1) % decide (exists (u\ (and ...)))
(maxt a % exist (NB dummy existential, here as a delay)
(max1 % release
(max2 % and-
  (maxi (ix 3) % store (ng (s (f a)))
  (maxi (ix 2) % decide (exists (y\ (or ...)))
  (maxt (skf1 a) % exist
  (max1 % release
  (max1 % or-
  (maxi (ix 4) % store (s (f a))
  (maxi (ix 5) % store (ng q)
  (maxi (ix 4) % decide (s (f a))
  (maxa (ix 3) % init (ng (s (f a)))
  )))))))))
  (maxi (ix 3) % store (ng q)
  (maxi (ix 2) % decide (exists (y\ (or ...)))
  (maxt a % exist
  (max1 % release
  (max1 % or-
  (maxi (ix 4) % store (s a)
  (maxi (ix 5) % store q
  (maxi (ix 5) % decide q
  (maxa (ix 3) % init (ng q)
  )))))))))
))))))))
(or (exists (u\ forall (x\ (and (ng (s x)) (ng q)))))
    (exists (y\ (or  (s y)  q)))).

% Inner skolemization also allows for this proof, where we decide
% first on the second formula
example 6
(max 1
(max1 % or-
(maxi (ix 1) % store (exists (y\ (or ...)))
(maxi (ix 2) % store (exists (u\ (and ...)))
(maxi (ix 1) % decide (exists (y\ (or ...)))
(maxt a % exist (NB This time not a dummy! Deciding on the second E)
(max1 % release
(max1 % or-
(maxi (ix 3) % store (s a)
(maxi (ix 4) % store q
(maxi (ix 2) % decide (exists (u\ (and ...)))
(maxt a % exist (dummy existential)
(max1 % release
(max2 % and-
  (maxi (ix 5) % store (ng (s a))
  (maxi (ix 3) % decide (s a)
  (maxa (ix 5) % init (ng (s a))
  )))
  (maxi (ix 5) % store (ng q)
  (maxi (ix 4) % decide q
  (maxa (ix 5) % init (ng q)
  )))
))))))))))))))
(or (exists (u\ (and (ng (s a))  (ng q))))
    (exists (y\ (or  (s y)  q)))).


%(max 1 (max1 (maxi (ix 1) (maxi (ix 2) (maxi (ix 1) (maxt a (max1 (max1 (maxi (ix 3) (maxi (ix 4) (maxi (ix 2) (maxt a (max1 (max2 (maxi (ix 5) (maxi (ix 3) (maxa (ix 5) )))  (maxi (ix 5)   (maxi (ix 4)   (maxa (ix 5)   )))))))))))))))))


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test I   :- example I Cert Form, polarize Form B, lkf_entry Cert B.

test_all :- example I Cert Form, polarize Form B,
            term_to_string I Str, print Str, print "  ", 
            test_spec Cert B, print "\n", fail.

test_spec Cert B :- (lkf_entry Cert B, print "#", fail) ; true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

polarize A      L :- pred_pname A Name Args, lit+ (atom Name Args) L.
polarize (ng A) L :- pred_pname A Name Args, lit- (atom Name Args) L.
polarize tt               A :- true-  A.
polarize ff               A :- false- A.
polarize (and B C)        A :- polarize B D, polarize C E, conj- D E A.
polarize (or  B C)        A :- polarize B D, polarize C E, disj- D E A.
polarize (imp B C)        A :- polarize (ng B) D, polarize C E, disj- D E A.
polarize (equiv B C)      A :- polarize (imp B C) D, polarize (imp C B) E, conj- D E A.
polarize (ng (ng B))      C :- polarize B C.
polarize (ng (and B C))   A :- polarize (ng B) D, polarize (ng C) E, disj- D E A.
polarize (ng (or  B C))   A :- polarize (ng B) D, polarize (ng C) E, conj- D E A.
polarize (ng (imp B C))   A :- polarize B D,      polarize (ng C) E, conj- D E A.
polarize (ng (equiv B C)) A :- polarize (ng (imp B C)) D, 
                               polarize (ng (imp C B)) E, disj- D E A.
polarize (forall B)      A :- (pi x\ polarize (B x) (D x)),      all-  D A.
polarize (ng (exists B)) A :- (pi x\ polarize (ng (B x)) (D x)), all-  D A.
polarize (exists B)      A :- (pi x\ polarize (B x)  (D x)), some+ D A.
polarize (ng (forall B)) A :- (pi x\ polarize (ng (B x)) (D x)), some+ D A.
