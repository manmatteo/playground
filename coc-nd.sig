sig coc-nd.
kind term type.
type fun  term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
type app  list term -> term.

type of term -> term -> o.
type beta term -> term -> o.

kind s type.
type p s. % sort prop
type t s. % sort type
type sort s -> term.
type axiom s -> s -> o.
type rel s -> s -> s -> o.
