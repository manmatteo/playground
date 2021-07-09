module coc-ljf.
accum_sig pts-certificates.

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
% asyncr Cert (fun A T) (unk (prod A B)) :-
%   prodR_jc Cert Sort SortCert Cert',
%   asyncr SortCert (prod A B) (unk (sort (n Sort))),
%   asyncl Cert' [A] T (x\ unk (B x)).
asyncr Cert (fun A T) (unk (prod A B)) :-
  prodR_jc Cert Sort SortCert Cert',
  asyncr SortCert (prod A B) (unk (sort (n Sort))),
  asyncl Cert' [A] T (x\ unk (B x)).
% Pl
% syncl Cert (prod A B) (P ` L) R :-
%   prodL_je Cert Sort SortCert Cert1 Cert2,
%   asyncr   SortCert (prod A B) (unk (sort (n Sort))),
%   syncr    Cert1 P A,
%   syncl    (Cert2 Cert1) (B P) L R.
syncl Cert (prod A B) (P ` L) R :-
  prodL_je Cert Sort SortCert Cert1 Cert2,
  asyncr   SortCert (prod A B) (unk (sort (n Sort))),
  syncr    Cert1 P A,
  syncl    (Cert2 Cert1) (B P) L R.

% %% sort
% asyncr Cert (sort X) (unk (sort Y)) :-
%   sorted_jc Cert,
%   unpol X X', unpol Y Y',
%   axiom X' Y'.

% New sorting rule

% Works fine, but what if I want to start from asyncr?
% Cuts at the end of these axioms: otherwise there's some wild nondeterminism with the usual axiom rule.
syncl Cert (sort X) # (sort X) :-
  sorted_jc Cert, % TODO fix
  % unpol X X', % Here I actually want to check whether X is sorted by a positive sort!! This is an argument in favour of having axioms for polarized sorts
  axiom X _Y,!. % Molto TODO

syncr Cert (sort X) (sort Y) :-
  sorted_jc Cert,
  % unpol X X', unpol Y Y',
  axiom X Y,!.
% asyncr Cert (sort X) (unk (sort Y)) :-
%   sorted_jc Cert,
%   axiom X Y.

% asyncr Cert (prod A B) (str (sort (n S3))) :-
%   prodsort_jc Cert S1 Cert1 S2 Cert2,
%   rel S1' S2' S3,
%   pol S1' S1, pol S2' S2,
%   asyncr Cert1 A (unk (sort S1)),
%   asyncl Cert2 [A] B (x\ unk (sort S2)).

asyncr Cert (prod A B) (str (sort (n S3))) :- % Store è gratis: tanto vale assumere che sia fatto
  prodsort_jc Cert S1 Cert1 S2 _Cert2,
  rel S1 S2 (n S3),
  % pol S1' S1, pol S2' S2,
  syncr Cert1 A (sort S1),
  pi x\ pi index\ store index x A => (syncr Cert1 (B x) (sort S2)).
  % syncl Cert1 (sort (n S3)) Cont (sort (n S3)). % TODO Fix certificate

%% ax
syncl Cert N # N :-
  axiomL_je Cert Sort SortCert,
  syncr SortCert N (sort (n Sort)).
syncr Cert Var P :-
  axiomR_je Cert Sort SortCert Index,
  store Index Var P,
  syncr SortCert P (sort (p Sort)).

%% structural
% decide_l
asyncr Cert (app Var L) (str R) :-
  decideL_jc Cert Sort SortCert Cert' Index,
  % print "Enter decide...",
  store Index Var N,
  % print "Select" N "at" Var,
  syncr SortCert N (sort (n Sort)),
  % print "Decide on" Var "of" N,
  syncl Cert' N L R.
  % print "Success decide".
% decide_r
asyncr Cert (posbox P) (str R) :-
  decideR_jc Cert Sort SortCert Cert',
  syncr SortCert R (sort (p Sort)),
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
  syncr SortCert N (sort (n Sort)),
  asyncr Cert' T (unk N).
  % print "Success release_r".
%release_l
syncl Cert P (kappa P T) A :-
  % print "Enter release_l",
  releaseL_je Cert Sort SortCert Cert',
  syncr SortCert P (sort (p Sort)),
  asyncl Cert' [P] T (x\ str A).
  % print "Success release_l".

%% Placeholder. Currently unused in the kernel.
beta X X.
