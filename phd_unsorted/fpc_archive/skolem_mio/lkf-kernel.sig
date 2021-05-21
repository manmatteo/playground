sig lkf-kernel.
accum_sig lkf-certificates.
accum_sig lib.

accum_sig classical.

type lkf_entry      cert -> form -> o.

/* sequents */
type async           cert -> list form -> o.
type sync            cert ->      form -> o.
type storage        index ->      form -> o.
/* end */


% The following needed for translating client-side to kernal-side terms.
%type dummy             i.
type rigid             i -> o.
type ready, notready   cp -> o.

kind cp            type.
type cp            i -> i -> cp.
type cc            list cp -> cp -> o.
type cc_interp     list cp -> list cp -> o.

type localcp       i -> i -> o.
type ck_translate  i -> i -> o.
