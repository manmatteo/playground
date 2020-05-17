sig ljf-kernel.
accum_sig util.
accum_sig ljf-certificates.

type ljf_entry      cert -> form -> prop.

%  The following should be hidden in the .mod file.

kind rhs                                 type.   % The RHS of the async sequent
type unk                          form -> rhs.   % The right-hand-side is either unknown or stored.
type str                                  rhs.   % New: a stored RHS is all in the storage area!

kind seq                                 type.   % sequents
type async           list form -> rhs  -> seq.   % async
type lfoc                         form -> seq.   % left focus
type rfoc                         form -> seq.   % right focus
type storagel, storager index -> form -> prop.   % storage of formulas
type check               cert -> seq  -> prop.   % top-level predicate
