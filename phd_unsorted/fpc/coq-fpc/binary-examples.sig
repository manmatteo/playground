sig binary-examples.
accum_sig lkf-kernel, lkf-polarize.
accum_sig binary-fpc.
accum_sig lists.

type example               int -> list cform -> list cform -> list method -> prop.

type assume_lemmas         int -> list cform -> prop -> prop.
type print_clause          int -> form -> prop.

type test_all                     prop.
type test_resol'           int -> prop.
type test_resol            int -> prop.

% Client supplied constants contained in resolution clauses

type z                  i.
type k             i -> i.
type a, b, e        cform.
type r, t      i -> cform.

type test   int -> form -> prop.
