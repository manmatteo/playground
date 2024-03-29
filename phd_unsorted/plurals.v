(* A stub about parthood and plurals in a mereological setting, inspired by the lectures in linguistics at ENS during Spring 2020 *)
Class N.
Parameter part: N -> N -> Prop.

Notation "A '<=' b" := (part A b) (at level 70).

Axiom isEpsilon : forall A a,
iff (A <= a) ((exists B, B <= A) /\ (forall C D, (C<A/\D<A->C<D))/\(forall C,C<A->C<a)).

Definition Atomic X := ~ exists 
