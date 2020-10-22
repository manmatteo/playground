kind term type.
type fun  term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
type app  list term -> term.

type store term -> term -> prop.

type sync  list term -> term -> term -> prop.
type async term -> term -> prop.
type astr  term -> term -> prop.

kind s type.
type p s. % sort prop
type t s. % sort type
type sort s -> term.
type axiom s -> s -> prop.
