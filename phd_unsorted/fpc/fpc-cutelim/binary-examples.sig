sig binary-examples.
accum_sig lkf-kernel, lkf-polarize.
accum_sig binary-fpc.
accum_sig lists.

type example               int -> list cform -> list cform -> list method -> o.

type assume_lemmas         int -> list cform -> o -> o.
type print_clause          int -> form -> o.

type test_all                     o.
type test_resol'           int -> o.
type test_resol            int -> o.

% Client supplied constants contained in resolution clauses

type z                  i.
type k             i -> i.
type a, b, e        cform.
type r, t      i -> cform.

type test   int -> form -> o.
