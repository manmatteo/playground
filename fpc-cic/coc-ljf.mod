module coc-ljf.
accum_sig pts-certificates.

:if "DEBUG" asyncl A B C D :- print "asyncl" A B C D, fail.
:if "DEBUG" asyncr A B C :- print "asyncr" A B C, fail.
:if "DEBUG" syncr  A B C :- print "syncr" A B C, fail.
:if "DEBUG" syncl  A B C D :- print "syncl" A B C D, fail.

%% sort
asyncr Cert (sort X) (str (sort Y)) :-
  sorted_jc Cert,
  axiom X Y.

asyncr Cert (prod _Name A B) (str (sort S3)) :-
  prodsort_jc Cert Sort Cert1 Sort Cert2,
  rel S1 S2 S3,
  asyncr Cert1 A (str (sort S1)),
  asyncl Cert2 [A] B (x\ str (sort S2)).

%% ax
syncl Cert N [] N :-
  axiomL_je Cert Sort SortCert,
  sortn Sort,
  asyncr SortCert N (str (sort Sort)).
syncr Cert Var P :-
  axiomR_je Cert Sort SortCert Index,
  store Index Var P,
  sortp Sort,
  asyncr SortCert P (str (sort Sort)).

%% structural
% decide_l
asyncr Cert (app [Var| L]) (str R) :-
  decideL_jc Cert Sort SortCert Cert' Index,
  store Index Var N,
  sortn Sort,
  asyncr SortCert N (str (sort Sort)),
  syncl Cert' N L R.
% decide_r
asyncr Cert (posbox P) (str R) :-
  decideR_jc Cert Sort SortCert Cert',
  sortp Sort,
  asyncr SortCert R (str (sort Sort)),
  syncr Cert' P R.
% store_r
asyncr Cert (negbox T) (unk A) :-
  storeR_jc Cert Cert',
  asyncr Cert' T (str A).
% store_l
asyncl Cert [N] T R :-
  storeL_jc Cert Index Sort SortCert,
  sortn Sort,
  asyncr SortCert N (str (sort Sort)),
  pi w\ store (Index (#idx w)) w N => asyncr (Cert (#cert w)) (T w) (R w).
%release_r
syncr Cert (posbox T) N :-
  releaseR_je Cert Sort SortCert Cert',
  sortn Sort,
  asyncr SortCert N (str (sort Sort)),
  asyncr Cert' T (unk N).
%release_l
syncl Cert P (kappa _Name P T) A :-
  releaseL_je Cert Sort SortCert Cert',
  sortp Sort,
  asyncr SortCert P (str (sort Sort)),
  asyncl Cert' [P] T (x\ str A).

%% prod
% Pr
asyncr Cert (fun _Name A T) (unk (prod _Name A B)) :-
  prodR_jc Cert Sort SortCert Cert',
  asyncr SortCert (prod _Name A B) (str (sort Sort)),
  asyncl Cert' [A] T (x\ unk (B x)).
% Pl
syncl Cert (prod _Name A B) [P | L] R :-
  prodL_je Cert Sort SortCert Cert1 Cert2,
  asyncr   SortCert (prod _Name A B) (str (sort Sort)),
  syncr    Cert1 P A,
  syncl    (Cert2 Cert1) (B P) L R.
  
%% Placeholder. Currently unused in the kernel.
beta X X.
