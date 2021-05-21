sig geo-examples.
accum_sig lkf-formulas, lkf-certificates.
accum_sig classical, classical-examples.
accum_sig geo-fpc.
accum_sig lkf-kernel.

type coe  bool -> atm.

type check   int -> o.
type geothm  int -> list index -> list bool -> bool -> cert -> o.
type theory   index -> bool -> o.
type polarize_fc, polarize_g, polarize_h    bool -> form -> o.


type sk1    i -> i.
type sk2    i -> i -> i.
type sk3    i -> i -> i -> i.


