% Signature for first-order classical logic formulas.

sig classical.
accum_sig lib.

kind i                          type.
kind bool                       type.

type tt, ff                     bool.
type ng                     	bool -> bool.
type and, or, imp, equiv    	bool -> bool -> bool.
type forall, exists             (i -> bool) -> bool.

type pred_pname    bool -> string -> list i -> o.
type fun_pname     i    -> string -> list i -> o.

type atomic        bool -> o.

type copyi         i -> i -> o.
type copybool      bool -> bool -> o.


% First-order terms
type a        i.
type b        i.
type c        i.
type d        i.
type e        i.
type n1, n2, n3, n4, n5  i.

type f        i -> i.
type f        i -> i.
type h        i -> i -> i.
type g        i -> i -> i.

% Predicates in the "client space"
type m        bool.
type mm       bool.
type q        bool.
type qq       bool.
type s        i -> bool.
type r        i -> i -> bool.
