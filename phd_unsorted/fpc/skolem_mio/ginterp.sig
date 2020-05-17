sig ginterp.
accum_sig lib.
accum_sig classical.

type positive, gclause     bool -> o.

type async       list bool -> list bool -> bool -> cert -> o.
type  syncL      list bool ->      bool -> bool -> cert -> o.
type  syncR      list bool              -> bool         -> o.

type theory      index -> bool -> o.
type gexample    int -> list bool -> bool -> cert -> o.
type test        int -> o.

type sk1    i -> i.
type sk2    i -> i -> i.
type sk3    i -> i -> i -> i.

type sk1serial, sk2directed, sk3directed index.

type skolemized    bool -> bool -> o.
type sk_positive   bool -> bool -> o.

kind  index      type.
type  trans, directed, ref, sym, euclidean, connected, serial    index.

kind  cert       type.
type  evar       (i -> cert) -> cert.
type  done       cert.
type  inst       i -> cert -> cert.
type  decide     index -> cert -> cert.


