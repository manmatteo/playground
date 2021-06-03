sig coc-ljf.

kind continuation type.
type # continuation.
type ` term -> continuation -> continuation.
infix ` 120.

kind term type.
type fun   term -> (term -> term) -> term.
type prod  term -> (term -> term) -> term.
type kappa term -> (term -> term) -> continuation.
type app   continuation -> term.
type posbox term -> term.
type negbox term -> term.

kind s type. % sorts
% type sort  s -> term.
kind ps type. % polarized sorts
type p s -> ps.
type n s -> ps.
type sort ps -> term.
type pol   s -> ps -> prop.
type unpol ps -> s -> prop.
type axiom s -> s -> prop.
type rel s -> s -> s -> prop.

type beta  term -> term -> prop.

kind index type.
type store index -> term -> term -> prop.

type #idx  term -> index.
type #cert term -> cert.

kind cert type.
kind rhs type.
type str term -> rhs.
type unk term -> rhs.
type asyncl (cert -> cert) -> list term -> (term -> term) -> (term -> rhs) -> prop.
type asyncr cert ->                        term -> rhs -> prop.
type syncl  cert ->          term -> continuation -> term -> prop.
type syncr  cert ->                       term -> term -> prop.
