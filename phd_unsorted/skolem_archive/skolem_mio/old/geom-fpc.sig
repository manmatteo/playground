% This is a non-standard header.  Get this fpc to conform.
sig geom-fpc.

accum_sig lkf-certificates.
accum_sig lib.
accum_sig classical.

kind pair     type -> type -> type.
type pr       A -> B -> pair A B.

type idx             int -> index.
typeabbrev assoc     list (pair i i).     % Association of internal/external eigenvariables
typeabbrev context   list (pair form int). % Basic elements of contexts

type istate            assoc -> context -> (list int)     -> cert.
type astate            assoc -> context -> (list int)     -> cert.
type sstate            assoc -> context -> (list int)-> cert.

type translate_term    assoc -> i -> i -> o.