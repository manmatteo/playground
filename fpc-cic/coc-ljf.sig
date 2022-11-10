sig coc-ljf.

kind continuation type.
type nl continuation.
type (`) val -> continuation -> continuation.
% infixr ` 120.

kind term type.
kind val type.
type fun   val -> (val -> term) -> term.
type prod  val -> (val -> val) -> continuation -> term.
type kappa val -> (val -> term) -> continuation.
% Note that this was wrong in Taus' PPDP15 paper
type app   val -> continuation -> term.
type posbox val -> term.
type negbox term -> val.

%% NOTE: sorts, axioms, relations have been moved to certificates!
type pol   s -> ps -> prop.
type unpol ps -> s -> prop.

type beta  term -> term -> prop.

kind index type.
type store index -> val -> val -> prop.
type named val -> val -> val -> prop.

type to_idx  val -> index.
type to_cert val -> cert.

kind cert type.
kind rhs type.
type str val -> rhs.
type unk val -> rhs.
type asyncl (cert -> cert) -> list val -> (val -> term) -> (val -> rhs) -> prop.
type asyncr cert ->                        term -> rhs -> prop.
type syncl  cert ->          val -> continuation -> val -> prop.
type syncr  cert ->                       val -> val -> prop.
