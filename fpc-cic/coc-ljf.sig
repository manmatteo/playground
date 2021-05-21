sig coc-ljf.
kind term type.
type fun  string -> term -> (term -> term) -> term.
type prod string -> term -> (term -> term) -> term.
type app  (list term) -> term.

type beta  term -> term -> o.

type store term -> term -> o.
type negatm term -> o.
type posatm term -> o.

kind cert type.
type sync   (cert -> cert) -> term -> (cert -> term) -> o.
type asyncl (cert -> cert) -> term -> (cert -> term) -> o.
type asyncr cert -> term -> o.
type astr   cert -> term -> o.

kind s type.
type p s. % sort prop
type t s. % sort type
type sort s -> term.
type axiom s -> s -> o.
type rel s -> s -> s -> o.
