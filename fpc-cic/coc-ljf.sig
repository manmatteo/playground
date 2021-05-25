sig coc-ljf.
kind term type.
type fun   string -> term -> (term -> term) -> term.
type prod  string -> term -> (term -> term) -> term.
type kappa string -> term -> (term -> term) -> list term.
type app   (list term) -> term.
type posbox term -> term.
type negbox term -> term.

kind s type. % sorts
type sort s -> term.
type sortp s -> prop.
type sortn s -> prop.
type axiom s -> s -> o.
type rel s -> s -> s -> o.

type beta  term -> term -> o.

kind index type.
type store index -> term -> term -> o.

type #idx  term -> index.
type #cert term -> cert.

kind cert type.
kind rhs type.
type str term -> rhs.
type unk term -> rhs.
type asyncl (cert -> cert) -> list term -> (term -> term) -> (term -> rhs) -> prop.
type asyncr cert ->                        term -> rhs -> prop.
type syncl  cert ->          term -> list term -> term -> prop.
type syncr  cert ->                       term -> term -> prop.
