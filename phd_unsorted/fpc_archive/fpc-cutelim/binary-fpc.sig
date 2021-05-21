sig binary-fpc.
accum_sig lkf-certificates.

/* start */
type idx      int -> index.
type start    int -> list method -> cert.
/* end */

/* cut */
kind method   type.
type resol    int -> int -> int -> method.
type rlist            list method -> cert.
type rlisti   int ->  list method -> cert.
type rdone                           cert.
type lemma    int -> form -> o.
/* end */

/* dlist */
type lit             index.
type dlist           list int    -> cert.
/* end */

/* factor */
type factor          int -> int -> method.
type factr                 int    -> cert.
type fdone                           cert.
/* end */
