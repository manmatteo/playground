sig lkf-kernel.
accum_sig lkf-certificates.
accum_sig spy.

type lkf_entry      cert -> form -> prop.

/* sequents */
kind seq                         type.
type unf             list form -> seq.
type foc                  form -> seq.
type storage       index -> form -> prop.
/* end */

/* simple */
type check           cert -> seq -> prop.
/* end */
