module geo-fpc.

orC    (initialize Clauses Cert)         (initialize Clauses Cert).
storeC (initialize [Index|Clauses] Cert) (initialize Clauses Cert) Index.
storeC (initialize [] Cert) (asyn Cert) indx.
storeC (asyn Cert) (asyn Cert) indx.
orC    (asyn Cert) (asyn Cert).

decideE   (asyn (decide Index Cert)) (syn Cert) Index.
decideE   (asyn done)   finish indx.

someE     (syn (inst T Cert)) (syn Cert) T.
andE      (syn Cert) immediate (syn Cert).
initialE  immediate indx.

releaseE  (syn Cert) (asyn Cert).

allC      (asyn (evar Cert)) (x\ asyn (Cert x)).
andC      (asyn (andc Cert Cert')) (asyn Cert) (asyn Cert').

someE     finish finish T.
andE      finish finish finish.
orE       finish finish Choice.
initialE  finish indx.
