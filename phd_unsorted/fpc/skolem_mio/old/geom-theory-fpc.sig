% This is a non-standard header.  Get this fpc to conform.
sig geom-fpc.

accum_sig lkf-certificates.
accum_sig lib.
accum_sig classical.

kind pair     type -> type -> type.
type pr       A -> B -> pair A B.

type idx             int -> index.
typeabbrev assoc     list (pair i i).     % Association of internal/external eigenvariables
typeabbrev context   list (pair form int). % Basic elements of contexts

type istate            assoc -> context -> (list int)     -> cert.
type astate            assoc -> context -> (list int)     -> cert.
type sstate            assoc -> context -> (list int)-> cert.

type translate_term    assoc -> i -> i -> o.

%% Imported

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

type  trans, directed, ref, sym, euclidean, connected, serial    index.

type  evar       (i -> cert) -> cert.
type  done       cert.
type  inst       i -> cert -> cert.
type  decide     index -> cert -> cert.