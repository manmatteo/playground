sig coc-ljt.
kind term type.
type fun  term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
type app  (list term) -> term.

type beta  term -> term -> o.

type store term -> term -> o.
type negatm term -> o.

type sync  list term -> term -> term -> o.
type async term -> term -> o.
type astr  term -> term -> o.

kind s type.
type p s. % sort prop
type t s. % sort type
type sort s -> term.
type axiom s -> s -> o.
type rel s -> s -> s -> o.
