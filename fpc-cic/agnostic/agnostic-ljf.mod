% An attempt at writing an agnostic (i.e. without terms) version of the polarized PTS calculus
module coc-ljf.
accum_sig agnostic-certificates.

:if "DEBUG:kernel" asyncl A B C D :- print "asyncl" A B C D, fail.
:if "DEBUG:kernel" asyncr A B C :- print "asyncr" A B C, fail.
:if "DEBUG:kernel" syncr  A B C :- print "syncr" A B C, fail.
:if "DEBUG:kernel" syncl  A B C D :- print "syncl" A B C D, fail.

unpol (n X) X.
unpol (p X) X.
pol X (p X).
pol X (n X).

%% prod
% Pr
asyncr Cert (unk (prod A B)) :-
  prodR_jc Cert Sort Cert',
  asyncr (prod A B) (unk Sort),
  asyncl Cert' [A] (x\ unk (B x)),
  syncl Cert'.
% Pl
syncl Cert (prod A B) R :-
  prodL_je Cert Sort Cert1 Cert2,
  asyncr   (prod A B) (unk Sort),
  syncr    Cert1 A,
  syncl    (Cert2 Cert1) (B Cert1) R.

% Sorting
syncl Cert SortX SortX :-
  sorted_jc Cert. % TODO fix
  % unpol X X', % Here I actually want to check whether X is sorted by a positive sort!! This is an argument in favour of having axioms for polarized sorts
  % axiom X _Y. % Molto TODO

syncr SortX SortY :-
  sorted_jc SortX SortY.

asyncr (prod A B) (str S3) :- % Store è gratis: tanto vale assumere che sia fatto
  prodsort_jc S1 S2 S3,
  syncr A S1,
  pi x\ pi index\ store index A => (syncr (B x) S2).
  % syncl Cert1 S3 S3.

%% ax
syncl Cert N N :-
  axiomL_je Cert NSort,
  syncr N NSort.
syncr Cert P :-
  axiomR_je Cert PSort Index,
  store Index P,
  syncr P PSort.

%% structural
% decide_l
asyncr Cert (str R) :-
  decideL_jc Cert NSort Cert' Index,
  store Index N,
  syncr N NSort
  syncl Cert' N R.
% decide_r
asyncr Cert (str R) :-
  decideR_jc Cert PSort Cert',
  syncr R PSort,
  syncr Cert' R.
% store_r
asyncr Cert (unk A) :-
  storeR_jc Cert Cert',
  asyncr Cert' (str A).
% store_l
asyncl Cert [N] R :-
  storeL_jc Cert Index,
  pi w\ store (Index w) N => asyncr (Cert w) (R w).
%release_r
syncr Cert N :-
  releaseR_je Cert NSort Cert',
  syncr N NSort,
  asyncr Cert' (unk N).
%release_l
syncl Cert P A :-
  releaseL_je Cert PSort Cert',
  syncr P PSort,
  asyncl Cert' [P] (x\ str A).

%% Placeholder. Currently unused in the kernel.
beta X X.

main :- print "OK".