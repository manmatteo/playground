module lkf-kernel.

lkf_entry Cert Form :- check Cert (unf [Form]).

% check A B         :- announce (check A B).
% check A (unf nil) :- announce (check A (unf nil)).
% store I C G       :- announce (store I C _).

store I C G :- storage I C => G.

check Cert (unf [C|Rest]) :- (isPos C ; isNegAtm C), store_kc Cert Cert' I, store I C (check Cert' (unf Rest)).
check Cert (unf nil)      :- decide_ke Cert Cert' I, storage I P, isPos P, check Cert' (foc P).
check Cert (unf nil)      :- cut_ke Cert CertA CertB F, negate F NF,       check CertA (unf [F]), check CertB (unf [NF]).

check Cert (unf [t-     |Rest]).
check Cert (unf [d- A   |Rest]) :-                             check Cert (unf [A|Rest]).
check Cert (unf [f-     |Rest]) :- false_kc  Cert Cert',       check Cert' (unf Rest).
check Cert (unf [A !-! B|Rest]) :- orNeg_kc  Cert Cert',       check Cert' (unf [A, B|Rest]).
check Cert (unf [A &-& B|Rest]) :- andNeg_kc Cert CertA CertB, check CertA (unf [A|Rest]), check CertB (unf [B|Rest]).
check Cert (unf [all B  |Rest]) :- all_kc    Cert Cert', pi w\ check (Cert' w) (unf [B w|Rest]).

check Cert (foc t+)        :- true_ke Cert.
check Cert (foc (p A))     :- initial_ke Cert I, storage I (n A).
check Cert (foc (d+ A))    :-                                     check Cert  (foc A).
check Cert (foc N)         :- isNeg N, release_ke Cert Cert',     check Cert' (unf [N]).
check Cert (foc (A &+& B)) :- andPos_ke Cert CertA CertB,         check CertA (foc A), check CertB (foc B).
check Cert (foc (some B))  :- some_ke  Cert Cert' T,              check Cert' (foc (B T)).
check Cert (foc (A !+! B)) :- orPos_ke Cert Cert' C, ((C = left,  check Cert' (foc A));
                                                      (C = right, check Cert' (foc B))).
