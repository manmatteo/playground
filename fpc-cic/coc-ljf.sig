sig coc-ljf.

kind continuation type.
type # continuation.
type ` term -> continuation -> continuation.
infixr ` 120.

kind term type.
type fun   term -> (term -> term) -> term.
type prod  term -> (term -> term) -> continuation -> term.
type kappa term -> (term -> term) -> continuation.
type app   term -> continuation -> term.
type posbox term -> term.
type negbox term -> term.

%% NOTE: sorts, axioms, relations have been moved to certificates!
type pol   s -> ps -> prop.
type unpol ps -> s -> prop.

type beta  term -> term -> prop.

kind index type.
type store index -> term -> term -> prop.
type named term -> term -> term -> prop.

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
