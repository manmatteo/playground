Goal forall P : nat -> Prop, let x := P 2 in x.
intros. simpl.
Abort.

Goal forall P : nat -> Prop, let x := 2 in (P x) -> P 2.
auto . Show Proof.