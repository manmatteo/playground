module ljf-kernel.
accumulate util.
accumulate ljf-formulas.

:if "DEBUG" check A B :- print "check" A B, fail.

ljf_entry Cert Form :- check Cert (async nil (unk Form)).

% Structural Rules
% decide
check Cert (async nil str) :-
  decideL_je Cert Cert' Index,
  storagel Index N,
  isNeg N, check Cert' (lfoc N).

check Cert (async nil str) :-
  decideR_je Cert Cert' Index, 
  storager Index P,
  isPos P, check Cert' (rfoc P).
% release
check Cert (lfoc P)   :- isPos P, releaseL_je Cert Cert', check Cert' (async [P] str).
check Cert (rfoc N)   :- isNeg N, releaseR_je Cert Cert', check Cert' (async nil (unk N)).
% store
check Cert (async [C|Theta] R) :-
  (isNeg C ; isPosAtm C),
  storeL_jc Cert Cert' Index,
  pi w\ storagel (Index w) C => 
    check (Cert' w) (async Theta R).
check Cert (async nil (unk D)) :-
  (isPos D ; isNegAtm D),
  storeR_jc Cert Cert' Index,
  pi w\ storager (Index w) D => 
    check (Cert' w) (async nil str).
% Identity rules
% initial
check Cert (lfoc Na) :- isNegAtm Na, initialL_je Cert, storager _Indx Na.
check Cert (rfoc Pa) :- isPosAtm Pa, initialR_je Cert Indx, storagel Indx Pa.
% cut
check Cert (async nil str) :- cut_je Cert CertA CertB F, 
 check CertA (async nil (unk F)), check CertB (async [F] str).

% Asynchronous Rules
% arrow
check Cert (async nil (unk (A arr B))) :-
  arr_jc Cert Cert',
  check Cert' (async [A] (unk B)).
% disjunction
check Cert (async [(A or+ B) | Theta] R) :-
  or_jc Cert CertA CertB,
  check CertA (async [A | Theta] R), check CertB (async [B | Theta] R).
% conjunction
check Cert  (async [(A and+ B) | Theta] R) :-
  andPos_jc Cert Cert',
  check Cert' (async [A , B | Theta] R).
check Cert (async nil (unk (A and- B))) :-
  andNeg_jc Cert CertA CertB,
  check CertA (async nil (unk A)), check CertB (async nil (unk B)).
% quantifers
% check Cert (async [some B | Theta] R) :-
%   std.map Cert some_jc Cert',
%   pi w\ check (Cert' w) (async [B w | Theta] R).
% check Cert (async nil (unk (all B))) :- all_jc Cert Cert',
%   pi w\ check (Cert' w) (async nil (unk (B w))).
% Units
check _Cert (async nil (unk t-)).
check Cert (async [f | _Theta] _R) :- false_jc Cert.
check Cert (async [t+| Theta] R) :- true_jc Cert Cert', check Cert' (async Theta R).
% Delays
% check Cert (async [d+ A|Theta] R)   :- check Cert (async [A|Theta] R).
% check Cert (async nil (unk (d- R))) :- check Cert (async nil (unk R)).

% Synchronous Rules
% arrow
check Cert (lfoc (A arr B)) :-
  arr_je Cert CertA CertB,
  check CertA (rfoc A), check CertB (lfoc B).
% % disjunction
% check Cert (rfoc (A or+ B)) :-
%   std.map Cert or_je Pair,
%   split Pair Cert' Choice, 
%   ((std.forall Choice (c\ c = left),  check Cert' (rfoc A)); (std.forall Choice (c\ c = right), check Cert' (rfoc B))).
% % conjunction
% check Cert (rfoc (A and+ B)) :- 
%   std.map Cert andPos_je Pairs,
%   split Pairs CertA CertB,
%   check CertA (rfoc A), check CertB (rfoc B).
% check Cert (lfoc (A and- B)) :-
%   std.map Cert andNeg_je Pairs,
%   split Pairs Cert' Choices,
%    ((std.forall Choices (c\ c = left), check Cert' (lfoc A));
%     (std.forall Choices (c\ c = right), check Cert' (lfoc B))).
% quantifers
% check Cert (rfoc (some B)) :- some_je Cert Cert' T, check Cert' (rfoc (B T)).
% check Cert (lfoc (all B) R) :- all_je Cert Cert' T, check Cert' (lfoc (B T) R).
% Units
check Cert (rfoc t+) :- true_je Cert.
% Delays
% check Cert (rfoc (d+ A))            :- check Cert (rfoc A). 
% check Cert (lfoc (d- A) R)          :- check Cert (lfoc A R) .
