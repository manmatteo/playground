sig geo-fpc.

accum_sig lkf-certificates.
accum_sig lib.

type  initialize list index -> cert -> cert.
type  asyn, syn           cert -> cert.
type  decide     index -> cert -> cert.
type  andc       cert -> cert -> cert.
type  immediate  cert.
type  finish     cert.
type  done       cert.
type  evar       (i -> cert) -> cert.
type  inst       i -> cert -> cert.

% Used a index for all stores that are not theory clauses.
type indx        index.  

