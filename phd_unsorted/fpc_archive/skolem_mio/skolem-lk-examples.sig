sig skolem-lk-examples.
accum_sig maxcert.
accum_sig lib.
accum_sig classical.
accum_sig lkf-formulas.
accum_sig lkf-kernel.

% Constructors for atoms and polarization
% type delay-, polarize  bool -> form -> o.

type sk1, sk2, sk3 i.
type skf1, skf2 i -> i.

type atom   string -> list i -> atm.

type example    int -> cert -> bool -> o.
type test       int -> o.
type check      cert -> form -> o.

type test_all   o.
type test_spec  cert -> form -> o.

type polarize bool -> form -> o.