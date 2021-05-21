% decide and existential decide depth fpc

% Keep two separate numbers: one for the maximum number occurrences of
% existential intro and one for the maximum number of non-existential
% (positive) introductions on any one path.

module ded-fpc.

andC         (ded D E) (ded D E) (ded D E).
falseC       (ded D E) (ded D E).
orC          (ded D E) (ded D E).
allC         (ded D E) (x\ ded D E).

storeC       (ded D E) (ded D E) indx.

orE          (ded D E) (ded D E) Choice.
andE         (ded D E) (ded D E) (ded D E).
someE        (ded D E) (ded D E) T.
releaseE     (ded D E) (ded D E).
initialE     (ded D E) indx.
trueE        (ded D E).
decideE      (ded D E) (dedx D E) indx.

orE          (dedx (succ D) E) (ded D E) Choice.
andE         (dedx (succ D) E) (ded D E) (ded D E).
someE        (dedx D (succ E)) (ded D E) T.
releaseE     (dedx (succ D) E) (ded D E).
initialE     (dedx (succ D) E) indx.
trueE        (dedx (succ D) E).

