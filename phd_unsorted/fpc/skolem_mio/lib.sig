sig lib.

type announce, spy    o -> o.
type bracket          string -> o -> string -> o.

type foreach            (A -> o) -> list A -> o.
type forsome            (A -> o) -> list A -> o.
type mappred            (A -> B -> o) -> list A -> list B -> o.
type mappred2           (A -> B -> C -> o) -> list A -> list B -> list C -> o.
type foldr              (A -> B -> B -> o) -> list A -> B -> B -> o.
type split              list A -> list A -> list A -> o.
type if                 o -> o -> o -> o.
type mapfun             (A -> B) -> list A -> list B -> o.
type memb               A -> list A -> o.
type memb_and_rest      A -> list A -> list A -> o.
type length             list A -> int -> o.

type append             list A -> list A -> list A -> o.
type join               list A -> list A -> list A -> o.
type inc                int -> int -> o.

type fix_bug            A -> o. % Teyjus has bugs with non-normal terms.  Printing forces normalization.

kind nat    type.
type zero   nat.
type succ   nat -> nat.

