sig exp-examples.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig exp-fpc.

% RB: The following, and their translations, are kept here. Should they be
% moved over to classical, or classical distributed? Everything is primed to
% avoid clashes with other modules and their shared definitions in classical.

% First-order terms
type a'        i.
type b'        i.
type c'        i.
type f'        i -> i.
type f         i -> i.
type h'        i -> i -> i.
type g        i -> i -> i.

% Predicates in the "client space"
type q'        bool.
type r'        i -> bool.
type q         i -> bool.
type s'        i -> i -> bool.

% Names provided for the internal space of formulas
type qq'       atm.
type rr'       i -> atm.
type ss'       i -> i -> atm.

type delay-, polarize  bool -> form -> o.

type example  int -> qet -> bool -> o.
type test     int -> o.
type check_exp  qet -> form -> o.

type test_all   o.
type test_spec  qet -> form -> o.

type translate bool -> et -> bool -> bool -> et -> bool -> o.

type skexample  int -> qet -> bool -> bool -> o.
