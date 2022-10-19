From elpi Require Import elpi.

Axiom C1 : Type.
Axiom C2 : Type.
Axiom c12 : C1 -> C2.
Axiom c1t : C1 -> Type.
Axiom c1f : C1 -> nat -> nat.

Elpi Command test.
Elpi Coercions On.

Elpi Query lp:{{
  coq.locate "c12" GR1,
  coq.locate "c1t"   GR2,
  coq.locate "c1f"   GR3,
  coq.locate "C1"    C1,
  @global! => coq.coercion.declare (coercion GR1 _ _ _),
  @global! => coq.coercion.declare (coercion GR2 _ C1 sortclass),
  @global! => coq.coercion.declare (coercion GR3 _ C1 funclass).
}}.

Check (fun x : C1 => (x : C2)).
Check (fun x : C1 => fun y : x => true).
Check (fun x : C1 => x 3).

Elpi Query lp:{{coq.coercion.db L}}.
