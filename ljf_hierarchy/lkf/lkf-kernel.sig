sig lkf-kernel.

accum_sig lkf-certificates, lkf-formulas.

type lkf_entry      cert -> form -> prop.

kind seq                         type.
type unf             list form -> seq.
type foc                  form -> seq.
type check           cert -> seq -> prop.
type storage       index -> form -> prop.
type store         index -> form -> prop -> prop.
