module coc-ljf.
accum_sig pts-certificates.

:if "DEBUG" asyncl A B C D :- print "asyncl" A B C D, fail.
:if "DEBUG" asyncr A B C :- print "asyncr" A B C, fail.
:if "DEBUG" syncr  A B C :- print "syncr" A B C, fail.
:if "DEBUG" syncl  A B C D :- print "syncl" A B C D, fail.

unpol (n X) X.
unpol (p X) X.
pol X (p X).
pol X (n X).

%% prod
% Pr
asyncr Cert (fun A T) (unk (prod A B)) :-
  prodR_jc Cert Sort SortCert Cert',
  % print "\nEnter Well-sorted product",
  asyncr SortCert (prod A B) (unk (sort (n Sort))),
  % print "Exit Well-sorted product\n",
  asyncl Cert' [A] T (x\ unk (B x)).
% Pl
syncl Cert (prod A B) (P ` L) R :-
  prodL_je Cert Sort SortCert Cert1 Cert2,
  asyncr   SortCert (prod A B) (unk (sort (n Sort))),
  syncr    Cert1 P A,
  syncl    (Cert2 Cert1) (B P) L R.

%% sort
asyncr Cert (sort X) (unk (sort Y)) :-
  sorted_jc Cert,
  unpol X X', unpol Y Y',
  axiom X' Y'.

asyncr Cert (prod A B) (unk (sort (n S3))) :-
  prodsort_jc Cert S1 Cert1 S2 Cert2,
  rel S1' S2' S3,
  pol S1' S1, pol S2' S2,
  asyncr Cert1 A (unk (sort S1)),
  asyncl Cert2 [A] B (x\ unk (sort S2)).

%% ax
syncl Cert N # N :-
  axiomL_je Cert Sort SortCert,
  asyncr SortCert N (unk (sort (n Sort))).
syncr Cert Var P :-
  axiomR_je Cert Sort SortCert Index,
  store Index Var P,
  asyncr SortCert P (unk (sort (p Sort))).

%% structural
% decide_l
asyncr Cert (app Var L) (str R) :-
  decideL_jc Cert Sort SortCert Cert' Index,
  % print "Enter decide...",
  store Index Var N,
  % print "Select" N "at" Var,
  asyncr SortCert N (unk (sort (n Sort))),
  % print "Decide on" Var "of" N,
  syncl Cert' N L R.
  % print "Success decide".
% decide_r
asyncr Cert (posbox P) (str R) :-
  decideR_jc Cert Sort SortCert Cert',
  asyncr SortCert R (unk (sort (p Sort))),
  syncr Cert' P R.
% store_r
asyncr Cert T (unk A) :-
  storeR_jc Cert Cert',
  asyncr Cert' T (str A).
% store_l
asyncl Cert [N] T R :-
  storeL_jc Cert Index _Sort _SortCert, %% TODO remove unneeded params
  pi w\ store (Index (#idx w)) w N => asyncr (Cert (#cert w)) (T w) (R w).
%release_r
syncr Cert (negbox T) N :-
  % print "Enter release_r",
  releaseR_je Cert Sort SortCert Cert',
  asyncr SortCert N (unk (sort (n Sort))),
  asyncr Cert' T (unk N).
  % print "Success release_r".
%release_l
syncl Cert P (kappa P T) A :-
  % print "Enter release_l",
  releaseL_je Cert Sort SortCert Cert',
  asyncr SortCert P (unk (sort (p Sort))),
  asyncl Cert' [P] T (x\ str A).
  % print "Success release_l".

%% Placeholder. Currently unused in the kernel.
beta X X.
