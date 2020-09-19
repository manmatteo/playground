(* Problems of classical focalization in Coq *)
From elpi Require Import elpi.
(* What was underlined by Pichon *)
Parameter a:Prop.
Inductive weird : Prop :=
  mmh:  (a -> False) -> weird.

Goal weird -> a.

Elpi Command test.
Elpi Query lp:{{
  coq.locate "bubu" (indt X),
  coq.env.indt X _ _ _ Type Kn Clauses.
}}.
