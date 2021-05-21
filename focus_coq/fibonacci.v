Goal forall fib : nat -> nat -> Prop,
fib 0 1 -> fib 1 1 ->
(forall n n1 n2 :nat, fib (n-2) n2 -> fib (n-1) n1 -> fib n (n1+n2))
->
exists m, fib 3 m.
intros; eexists. apply H1. simpl. exact H0; simpl.
apply H1; simpl. exact H. exact H0.
Show Proof. Restart.

intros; eexists.
apply (let x := H0 in H1 x). exact H0.
apply (let x := _ in H1 x). exact H. exact H0.
Show Proof.