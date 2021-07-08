sig coc-ljf.

kind term type.
kind cert type.
kind continuation type.
type # continuation.
type ` term -> continuation -> continuation.
infix ` 120.

% type fun   term -> (term -> term) -> term.
type prod  term -> (cert -> term) -> term.
% type kappa term -> (term -> term) -> continuation.
% type app   term -> continuation -> term.
% type posbox term -> term.
% type negbox term -> term.

kind s type. % sorts
% type sort  s -> term.
kind ps type. % polarized sorts
type p s -> ps.
type n s -> ps.
type sort ps -> term.
type pol   s -> ps -> prop.
type unpol ps -> s -> prop.
type axiom ps -> ps -> prop.
type rel ps -> ps -> ps -> prop.

type beta  term -> term -> prop.

kind index type.
type store index -> term -> prop.

% type #idx  term -> index.
% type #cert term -> cert.

kind rhs type.
type str term -> rhs.
type unk term -> rhs.
type asyncl (cert -> cert) -> list term -> (cert -> rhs) -> prop.
type asyncr cert ->                        rhs -> prop.
type syncl  cert ->           term ->      term -> prop.
type syncr  cert ->                        term -> prop.
