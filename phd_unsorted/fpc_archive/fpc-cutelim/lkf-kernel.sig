sig lkf-kernel.
accum_sig lkf-certificates.
accum_sig spy.

type lkf_entry      cert -> form -> o.

/* sequents */
kind seq                         type.
type unf             list form -> seq.
type foc                  form -> seq.
type storage       index -> form -> o.
/* end */

/* simple */
type check           cert -> seq -> o.
/* end */
