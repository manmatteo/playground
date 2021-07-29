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

% Names and maintenance
asyncr Cert T (unk (negbox A)) :-
  %% NOTE: If there's a negbox, then... There's no name?
  asyncr Cert T (unk A).

asyncr Cert T (unk (posbox N)) :-
  % named N A, NOTE: If there's a posbox, then either there's a name or it's initial
  asyncr Cert T (unk N).

asyncr Cert (prod A B (kappa Ty T)) (unk (prod A B (kappa Ty C))) :-
  pi w\ named w Ty (prod A B #) =>
    % (print "---New name" w "for" (prod A B #),
    asyncr Cert (T w) (unk (C w)).

asyncr Cert T (unk N) :-
  named N _Ty A,
  % print "---Retrieved" A "at" N,
  asyncr Cert T (unk A). 

syncl Cert (negbox A) Cont G :-
  syncl Cert A Cont G.

%% These look more or less like hacks at this point
syncr _Cert N Ty :-
  named N Ty _Def.
asyncr _Cert (prod A B Cont) (str Sort) :- 
  named _N Sort (prod A B Cont).
asyncr Cert (app Var L) (str R) :-
  decideL_jc Cert Sort _SortCert Cert' Index,
  store Index Var N,
  named N (sort (n Sort)) Def,
  syncl Cert' Def L R.

%% prod
% Pr
asyncr Cert (fun A T) (unk (prod A B # as Prod)) :-
  prodR_jc Cert Sort SortCert Cert',
  % print "---Check sort for prodR",
  asyncr SortCert Prod (unk (sort (n Sort))),
  % print "---Ok sort for prodR",
  asyncl Cert' [A] T (x\ unk (B x)).
% Pl
syncl Cert (prod A B _Cont as Prod) (P ` L) R :-
  prodL_je Cert Sort SortCert Cert1 Cert2,
  asyncr   SortCert Prod (unk (sort (n Sort))),
  syncr    Cert1 P A,
  syncl    (Cert2 Cert1) (B P) L R.

% %% sort
asyncr Cert (prod A B Cont) (str (sort (n S3))) :- % Store è gratis: tanto vale assumere che sia fatto
  prodsort_jc Cert S1 Cert1 S2 _Cert2,
  rel S1 S2 (n S3),
  % pol S1' S1, pol S2' S2,
  % print "---one",
  syncr Cert1 A (sort S1),
  % print "---one done; two",
  pi x\ store _Index x A => (syncr Cert1 (B x) (sort S2)),
  % print "---two done; three",
  % print "---Enter continuation",
  syncl Cert1 (sort (n S3)) Cont (sort (n S3)).
  % print "---Done continuation". % TODO Fix certificate
% Works fine, but what if I want to start from asyncr?
% Cuts at the end of these axioms: otherwise there's some wild nondeterminism with the usual axiom rule.
syncl Cert (sort X) # (sort X) :-
  sorted_jc Cert,
  (axiom X (n _Y); axiom _ X),!. %% Topmost sorts are always negative?

syncr Cert (sort X) (sort Y) :-
  sorted_jc Cert,
  % unpol X X', unpol Y Y',
  axiom X Y,!.

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
  store Index Var N,
  syncr SortCert N (sort (n Sort)),
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
  storeL_jc Cert Index _Sort _SortCert, %% TODO remove unneeded params
  pi w\ store (Index (#idx w)) w N => asyncr (Cert (#cert w)) (T w) (R w).
%release_r
syncr Cert (negbox T) N :-
  releaseR_je Cert Sort SortCert Cert',
  syncr SortCert N (sort (n Sort)),
  asyncr Cert' T (unk N).
%release_l
syncl Cert P (kappa P T) A :-
  releaseL_je Cert Sort SortCert Cert',
  syncr SortCert P (sort (p Sort)),
  asyncl Cert' [P] T (x\ str A).

%% Placeholder. Currently unused in the kernel.
beta X X.
