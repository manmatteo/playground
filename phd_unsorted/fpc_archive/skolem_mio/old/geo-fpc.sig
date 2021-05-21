sig geo-fpc.

accum_sig lkf-certificates.
accum_sig lib.
accum_sig classical.

type  trans, directed, ref, sym, euclidean, connected, serial    index.
type  sk1serial, sk2directed, sk3directed index.

type skolemized    bool -> bool -> o.
type sk_positive   bool -> bool -> o.

type  initialize list index -> cert -> cert.
type  evar              (i -> cert) -> cert.
type  done                             cert.
type  inst                i -> cert -> cert.
type  decide          index -> cert -> cert.
