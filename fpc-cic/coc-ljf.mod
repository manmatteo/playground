module coc-ljf.
accum_sig pts-certificates.
% shorten certificates.{ p, n, sort, axiom, rel, prodL_je, prodR_jc, releaseL_je, releaseR_je, decideL_jc, decideL_jc, decideR_jc, storeR_jc, storeL_jc, axiomL_je, axiomL_je, axiomR_je, prodsort_jc, sorted_jc }.

:if "DEBUG:kernel" asyncl A B C D :- print "asyncl" A B C D, fail.
:if "DEBUG:kernel" asyncr A B C :- print "asyncr" A B C, fail.
:if "DEBUG:kernel" syncr  A B C :- print "syncr" A B C, fail.
:if "DEBUG:kernel" syncl  A B C D :- print "syncl" A B C D, fail.

unpol (n X) X.
unpol (p X) X.
pol X (p X).
pol X (n X).

% Small hack: topmost sort is always treated as negative. This is because since there's no axiom about it, we don't know whether it's positive or negative
pred topmost_sort i:ps.
topmost_sort X :- axiom _ X, not (axiom X _).

% Names and maintenance

% To fix if I switch to vals!
% asyncr Cert T (unk (posbox N)) :-
%   % named N A, NOTE: If there's a posbox, then either there's a name or it's initial
%   asyncr Cert T (unk N).

% To fix if I switch to vals!
% asyncr Cert (prod A B (kappa Ty T)) (unk (prod A B (kappa Ty C))) :-
%   pi w\ named w Ty (prod A B nl) =>
%     % (print "---New name" w "for" (prod A B nl),
%     asyncr Cert (T w) (unk (C w)).

% To fix if I switch to vals!
% asyncr Cert T (unk N) :-
%   named N _Ty A,
%   % print "---Retrieved" A "at" N,
%   asyncr Cert T (unk A). 

%% These still look like hacks at this point
% syncr _Cert N Ty :-
%   named N Ty _Def.
% asyncr _Cert (prod A B Cont) (str Sort) :- 
%   named _N Sort (prod A B Cont).
% asyncr Cert (app Var L) (str R) :-
%   decideL_jc Cert Sort _SortCert Cert' Index,
%   store Index Var N,
%   named N (sort (n Sort)) Def,
%   syncl Cert' Def L R.

%% prod
% Pr
asyncr Cert (fun A T) (unk (negbox (prod A B nl) as Prod)) :-
  prodR_jc Cert Sort SortCert Cert',
  % print "---Check sort for prodR",
  syncr SortCert Prod (sort (n Sort)),
  % print "---Ok sort for prodR",
  asyncl Cert' [A] T (x\ unk (B x)).
% Pl
syncl Cert (negbox (prod A B _Cont) as Prod) (P ` L) R :-
  prodL_je Cert Sort SortCert Cert1 Cert2,
  % print "---Check sort for prodL on" Prod,
  syncr   SortCert Prod (sort (n Sort)),
  % print "---Ok sort for prodL on" Prod,
  % print "---prodl: one" Prod,
  syncr    Cert1 P A,
  % print "---prodl: two" Prod,
  cut_vvv P B B',
  % print "Voglio tagliare"  B,
  syncl    (Cert2 Cert1) B' L R.
  % print "---Ok prodL on" Prod "at lvl" Cert.

% %% sort
asyncr Cert (prod A B Cont) (str (sort (n S3))) :- % Store è gratis: tanto vale assumere che sia fatto
  prodsort_jc Cert S1 S2 (n S3) Index Cert1 Cert2 Cert3,
  rel S1 S2 (n S3),
  % pol S1' S1, pol S2' S2,
  % print "---one",
  syncr Cert1 A (sort S1),
  % print "---one done; two",
  pi x\ store Index x A => (syncr Cert2 (B x) (sort S2)),
  % print "---two done; three",
  % print "---Enter continuation",
  syncl Cert3 (sort (n S3)) Cont (sort (n S3)).%, print "---done prodsort!".
  % print "---Done continuation". % TODO Fix certificate
% Works fine, but what if I want to start from asyncr?
% Cuts at the end of these axioms: otherwise there's some wild nondeterminism with the usual axiom rule.
syncl Cert (sort X) nl (sort X) :-
  sorted_jc Cert,
  (axiom X (n _Y); topmost_sort X),!. %% Topmost sorts are always negative?

syncr Cert (sort X) (sort Y) :-
  sorted_jc Cert,
  % unpol X X', unpol Y Y',
  axiom X Y,!.

%% ax
syncl Cert N nl N :-
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
  store Index Var N,
  % print "---decide-sort for" N "at" Var,
  (syncr SortCert N (sort (n Sort)); N = sort X, topmost_sort X),
  % print "---decide-sort!",
  syncl Cert' N L R.
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
  storeL_jc Cert Index Cert',
  pi w\ store (Index (to_cert w)) w N => asyncr Cert' (T w) (R w).
%release_r
syncr Cert (negbox T) N :-
  releaseR_je Cert Sort SortCert Cert',
  % print "---SortCheck for release",
  (syncr SortCert N (sort (n Sort)) ; N = sort X, topmost_sort X),
  % print "---Done, release",
  asyncr Cert' T (unk N).
%release_l
syncl Cert P (kappa P T) A :-
  releaseL_je Cert Sort SortCert Cert',
  syncr SortCert P (sort (p Sort)),
  asyncl Cert' [P] T (x\ str A).

% Cut elimination in the style of Taus et al

pred cut_tkt i:term, i:continuation, o:term.
:if "DEBUG:cut" cut_tkt A B C :- print "cut_tkt" A B C, fail.
cut_tkt (fun _A T) (Q ` K) R :- cut_vtt Q T O, cut_tkt O K R.
cut_tkt (posbox Q) (kappa _A T) O :- cut_vtt Q T O.
cut_tkt (app X K) M (app X L) :- name X, cut_kapp K M L.

pred cut_kapp i:continuation, i:continuation, o:continuation.
:if "DEBUG:cut" cut_kapp A B C  :- print "cut_kapp" A B C, fail.
cut_kapp nl L L.
cut_kapp (H ` K) M (H ` L) :- cut_kapp K M L.
cut_kapp (kappa A T) M (kappa A L)   :- pi y\ cut_tkt (T y) M (L y).

pred cut_vtt i:val, i:(val -> term), o:term.
:if "DEBUG:cut" cut_vtt  A B C :- print "cut_vtt" A B C, fail.
cut_vtt X T (T X) :- name X.
cut_vtt (sort S) (x\ Q x) (Q (sort S)). %% Aggiunta io
cut_vtt P (x\ fun (A x) (y\ T x y)) (fun A' Q) :- cut_vvv P A A', pi y\ cut_vtt P (x\ T x y) (Q y).
cut_vtt P (x\ posbox (Q x)) (posbox R) :- cut_vvv P Q R.
cut_vtt P (x\ app Y (K x)) (app Y K') :- cut_vkk P K K'.
cut_vtt (negbox U) (x\ app x (K x)) U' :- cut_vkk (negbox U) K K', cut_tkt U K' U'.

cut_vtt P (x\ prod (A x) (y\ B x y) (K x)) (prod A' B' K') :- cut_vvv P A A', cut_vkk P K K', pi y\ cut_vvv P (x\ B x y) (B' y).

pred cut_vvv i:val, i:(val -> val), o:val.
:if "DEBUG:cut" cut_vvv  A B C :- print "cut_vvv" A B C, fail.
cut_vvv X (x\ Q x) (Q X) :- name X.
cut_vvv (sort S) (x\ Q x) (Q (sort S)). %% Aggiunta io
cut_vvv P (x\ x) P.
cut_vvv P_ (x\ Y) Y :- !.
cut_vvv P (x\ negbox (T x)) (negbox T') :- cut_vtt P T T'.

pred cut_vkk i:val, i:(val -> continuation), o:continuation.
:if "DEBUG:cut" cut_vkk  A B C :- print "cut_vkk" A B C, fail.
cut_vkk X (y\ K y) (K X) :- name X.
cut_vkk P_ (x\ nl)   nl.
cut_vkk P (x\ ((Q x) ` (K x))) (Q' ` K') :- cut_vvv P Q Q', cut_vkk P K K'.
cut_vkk P (x\ kappa (A x) (y\ T x y)) (kappa A' T') :- cut_vvv P A A', pi y\ cut_vtt P (x\ T x y) (T' y).