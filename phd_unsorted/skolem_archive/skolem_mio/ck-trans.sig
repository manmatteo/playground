sig ck-trans.
accum_sig lib.
accum_sig classical.
accum_sig lkf-certificates.

% The following needed for translating client-side to kernal-side terms.
type dummy             i.
type rigid             i -> o.
type ready, notready   cp -> o.

kind cp            type.
type cp            i -> i -> cp.
type cc            list cp -> cp -> o.
type cc_interp     list cp -> list cp -> o.

type localcp       i -> i -> o.
type ck_translate  i -> i -> o.
