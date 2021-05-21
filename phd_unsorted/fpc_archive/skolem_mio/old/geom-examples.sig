sig geom-examples.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig geom-fpc.

% RB: The following, and their translations, are kept here. Should they be
% moved over to classical, or classical distributed? Everything is primed to
% avoid clashes with other modules and their shared definitions in classical.

% First-order terms
type a        i.
type b        i.
type c        i.
type f        i -> i.
type h        i -> i -> i.
type g        i -> i -> i.
type n1, n2, n3, n4, n5   i.

% Predicates in the "client space"
type r        i -> i -> bool.
type q        i -> bool.
type s        i -> i -> bool.

% Names provided for the internal space of formulas
type qq'       atm.
type rr'       i -> atm.
type ss'       i -> i -> atm.

type delay-, polarize  bool -> form -> o.

type example  int -> (list int) -> bool -> o.
type test     int -> o.
type check_geom  (list int) -> form -> o.

type test_all   o.
type test_spec  (list int) -> form -> o.

% type translate bool -> et -> bool -> bool -> et -> bool -> o.

