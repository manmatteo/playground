module dd-fpc.

andC         (dd D) (dd D) (dd D).
falseC       (dd D) (dd D).
orC          (dd D) (dd D).
allC         (dd D) (x\ dd D).

storeC       (dd D) (dd D) indx.

orE          (dd D) (dd D) Choice.
andE         (dd D) (dd D) (dd D).
someE        (dd D) (dd D) T.
releaseE     (dd D) (dd D).
initialE     (dd D) indx.
trueE        (dd D).
decideE      (dd (succ D)) (dd D) indx.

