module maxcert.

% Maxcert as from the CADE2017 paper, patched with allCx for CSL2018

allC      (max N (maxv C ))         (x\ max N (C x)).
allCx     (max N C)         (max N C) Sk :- not (C = (maxv _)). % avoid overlap
andC   (max N (max2 A B))       (max N A) (max N B).
andE   (max N (max2 A B))       (max N A) (max N B).
cutE      (max N (maxf F A B))     (max N A) (max N B) F.
decideE   (max N (maxi I A))       (max N A) I.
storeC    (max N (maxi (ix N) A)) (max (N+1) A) (ix N).
falseC    (max N (max1 A))          (max N A).
orC    (max N (max1 A))          (max N A).
releaseE (max N (max1 A))          (max N A).
orE    (max N (maxc C A))       (max N A) C.
someE     (max N (maxt T A))       (max N A) T.
trueE     (max N   max0).
initialE (max N (maxa I)) I.