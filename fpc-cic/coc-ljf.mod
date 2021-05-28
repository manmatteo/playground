module coc-ljf.
accum_sig pts-certificates.

:if "DEBUG" asyncl A B C D :- print "asyncl" A B C D, fail.
:if "DEBUG" asyncr A B C :- print "asyncr" A B C, fail.
:if "DEBUG" syncr  A B C :- print "syncr" A B C, fail.
:if "DEBUG" syncl  A B C D :- print "syncl" A B C D, fail.

%% prod
% Pr
asyncr Cert (fun _Name A T) (unk (prod _Name A B)) :-
  prodR_jc Cert Sort SortCert Cert',
  print "\nEnter Well-sorted product",
  asyncr SortCert (prod _Name A B) (str (sort (n Sort))),
  print "Exit Well-sorted product\n",
  asyncl Cert' [A] T (x\ unk (B x)).
% Pl
syncl Cert (prod _Name A B) [P | L] R :-
  prodL_je Cert Sort SortCert Cert1 Cert2,
  asyncr   SortCert (prod _Name A B) (str (sort (n Sort))),
  syncr    Cert1 P A,
  syncl    (Cert2 Cert1) (B P) L R.

%% sort
asyncr Cert (sort (_ X)) (str (sort (_ Y))) :-
  sorted_jc Cert,
  axiom X Y.

asyncr Cert (prod _Name A B) (str (sort (_ S3))) :-
  prodsort_jc Cert (P1 S1) Cert1 (P2 S2) Cert2,
  rel S1 S2 S3,
  asyncr Cert1 A (str (sort (P1 S1))),
  asyncl Cert2 [A] B (x\ str (sort (P2 S2))).

%% ax
syncl Cert N [] N :-
  axiomL_je Cert Sort SortCert,
  asyncr SortCert N (str (sort (n Sort))).
syncr Cert Var P :-
  axiomR_je Cert Sort SortCert Index,
  store Index Var P,
  asyncr SortCert P (str (sort (p Sort))).

%% structural
% decide_l
asyncr Cert (app [Var| L]) (str R) :-
  decideL_jc Cert Sort SortCert Cert' Index,
  print "Enter decide...",
  store Index Var N,
  print "Select" N "at" Var,
  asyncr SortCert N (str (sort (n Sort))),
  print "Decide on" Var "of" N,
  syncl Cert' N L R,
  print "Success decide".
% decide_r
asyncr Cert (posbox P) (str R) :-
  decideR_jc Cert Sort SortCert Cert',
  asyncr SortCert R (str (sort (p Sort))),
  syncr Cert' P R.
% store_r
asyncr Cert (negbox T) (unk A) :-
  storeR_jc Cert Cert',
  asyncr Cert' T (str A).
% store_l
asyncl Cert [N] T R :-
  storeL_jc Cert Index Sort SortCert,
  % sortn Sort, Store anything!!
  % asyncr SortCert N (str (sort Sort)),
  pi w\ store (Index (#idx w)) w N => (print "Storing" N "at" w, asyncr (Cert (#cert w)) (T w) (R w)).
%release_r
syncr Cert (posbox T) N :-
  print "Enter release_r",
  releaseR_je Cert Sort SortCert Cert',
  asyncr SortCert N (str (sort (n Sort))),
  asyncr Cert' T (unk N),
  print "Success release_r".
%release_l
syncl Cert P (kappa _Name P T) A :-
  print "Enter release_l",
  releaseL_je Cert Sort SortCert Cert',
  asyncr SortCert P (str (sort (p Sort))),
  asyncl Cert' [P] T (x\ str A),
  print "Success release_l".

%% Placeholder. Currently unused in the kernel.
beta X X.
