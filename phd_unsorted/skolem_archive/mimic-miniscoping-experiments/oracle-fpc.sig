sig oracle-fpc.
accum_sig lkf-certificates.
/* start */
kind oracle          type.
type emp             oracle.                     % empty
type l, r            oracle -> oracle.           % left, right
type c               oracle -> oracle -> oracle. % conjunction
kind cert            type.
type start, restart  oracle -> cert.
type consume         oracle -> cert.
type root, lit       index.
/* end */
