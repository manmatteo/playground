Require Import dn_term.
Require Import dn_red.
Require Import dn_context.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.

(* Axiom and Relation part of our PTS are kept unknown, it is not usefull for now *)
Parameter Ax : Sorts -> Sorts -> Prop.
Parameter Rel : Sorts -> Sorts -> Sorts -> Prop.

(* Typing judgement *)
(* We only allow weakening on sorts and var and  we will prove later that
this give weakening on everythin *)
Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ⊣ " (at level 80, no associativity).

Inductive wf : Env -> Prop :=
 | wf_nil : nil ⊣
 | wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : DN_scope
with typ : Env -> Term -> Term -> Prop :=
 | cSort : forall Γ s t, Ax s t -> Γ ⊣ -> Γ  ⊢ !s : !t
 | cVar : forall  Γ A v, Γ ⊣ -> A ↓ v  ⊂ Γ -> Γ ⊢ #v : A 
 | cPi : forall Γ A B s t u, 
     Rel s t u -> Γ ⊢ A : !s -> A::Γ ⊢ B : !t -> Γ ⊢  Π(A), B : !u 
 | cLa : forall Γ A b B s, Γ ⊢  Π(A), B : !s ->
     A::Γ ⊢ b : B ->Γ ⊢ λ[A], b: Π(A), B
 | cApp : forall Γ a b A B ,Γ ⊢ a : Π(B), A -> Γ ⊢ b :  B -> Γ ⊢ a·b : A[←b]
 | Cnv : forall Γ a A B s,
      A ≡ B  -> Γ ⊢ a : A -> Γ ⊢ B : !s -> Γ ⊢ a : B
where "Γ ⊢ t : T" := (typ Γ t T) : DN_scope.

Hint Constructors wf typ.

Scheme typ_ind' := Induction for typ Sort Prop
      with wf_ind' := Induction for wf Sort Prop.

Combined Scheme typ_induc from typ_ind', wf_ind'.

Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣.
induction 1; eauto.
Qed.

Lemma wf_inv : forall A Γ, A::Γ ⊣ -> exists s, Γ ⊢ A: !s.
intros. inversion H; eauto.
Qed.

Hint Resolve wf_typ wf_inv.
(* Inversion Lemmas , one for each kind of term 
main shape : 
  if Γ ⊢ T : A and T is a (choose one sort/var/lambda/pi/app)
   then A must be equivalent to ...
*)
Lemma Geni_ : forall Γ T A, Γ ⊢ T : A ->
 (forall s, T = !s -> exists S, A ≡ !S /\ Ax s S).
induction 1; intros; try discriminate.
injection H1; intros; subst; clear H1.
exists t; intuition.
destruct (IHtyp1 s0 H2) as (t & ? & ?).
exists t; eauto.
Qed.

Lemma Geni : forall Γ s A, Γ ⊢ !s : A -> 
  (exists S, A ≡ !S /\ Ax s S).
intros.
apply (Geni_ Γ !s A); trivial.
Qed.

Lemma Genii_: forall Γ T A , Γ ⊢ T : A ->
 (forall x, T = #x -> exists A',  A ≡ A' /\ A' ↓ x ⊂ Γ ).
induction 1; intros; try discriminate.
injection H1; intros; subst; clear H1.
exists A; intuition.
destruct (IHtyp1 x H2) as (A' & ? & ?).
eauto.
Qed.

Lemma Genii : forall Γ x A, Γ ⊢ #x : A  ->
 (exists A' , A ≡ A' /\ A' ↓ x ⊂ Γ).
intros.
apply (Genii_ Γ #x A H x); trivial.
Qed.

Lemma Geniii_ : forall Γ T A, Γ ⊢ T : A ->
 (forall C D, T = Π(C), D -> exists s1, exists s2, exists s3, 
  ( A ≡ !s3 /\ Rel s1 s2 s3 /\ Γ ⊢ C : !s1  /\ C::Γ ⊢ D : !s2 )).
induction 1; intros; try discriminate. 
injection H2; intros; subst; clear H2.
exists s; exists t; exists u; eauto.
(*8*)
destruct (IHtyp1 C D H2) as (s1 & s2 & s3 & ?).
decompose [and] H3; clear H3.
exists s1; exists s2; exists s3; intuition.
eapply Betac_trans. apply Betac_sym. apply H. trivial.
Qed.

Lemma Geniii : forall Γ C D A, Γ ⊢ Π(C), D : A -> 
 (exists s1,exists s2,exists s3, 
     A ≡ !s3 /\ Rel s1 s2 s3 /\ Γ ⊢  C : !s1 /\ C::Γ ⊢ D : !s2 ).
intros.
apply (Geniii_ Γ  (Π(C), D) A); trivial.
Qed.

Lemma Geniv_ : forall Γ T A , Γ ⊢ T : A  ->
 (forall C d, T = λ[C], d -> exists s1, exists s2, exists s3, exists D, 
    A ≡ Π(C), D /\ Rel s1 s2 s3 /\ Γ ⊢ C : !s1 /\ C::Γ ⊢ d : D /\ C::Γ ⊢ D : !s2).
induction 1; intros; try discriminate. 
injection H1; intros; subst ; clear H1.
clear IHtyp1 IHtyp2. apply Geniii in H. destruct H as (s1 & t1 & u1 & ?  & ?  & ? & ?).
exists s1 ; exists t1; exists u1; exists B; intuition.
destruct (IHtyp1 C d H2) as (s1 & s2 & s3 & D & ?).
decompose [and] H3; clear H3.
exists s1; exists s2; exists s3; exists D; intuition.
eapply Betac_trans. apply Betac_sym. apply H. trivial.
Qed.

Lemma Geniv : forall Γ C d A, Γ ⊢ λ[C], d : A  ->
 (exists s1, exists s2, exists s3, exists D, 
  A ≡ Π(C), D /\ Rel s1 s2 s3 /\ Γ ⊢ C : !s1 /\ C::Γ ⊢ d : D /\ C::Γ ⊢ D : !s2 ).
intros.
apply (Geniv_ Γ (λ[C], d) A); trivial.
Qed.

Lemma Genv_ : forall Γ T A , Γ ⊢ T : A  ->
 (forall c d, T = c·d -> exists C, exists D, 
 A ≡ C[← d] /\ Γ ⊢ c : Π(D), C /\ Γ ⊢ d : D).
induction 1; intros; try discriminate.
injection H1; intros ; subst ; clear H1.
exists A; exists B; intuition.
destruct (IHtyp1 c d H2) as (C & D & ? & ? & ?).
exists C; exists D; intuition.
eapply Betac_trans. apply Betac_sym. apply H.
trivial.
Qed.

Lemma Genv : forall Γ c d A, Γ ⊢ c·d : A -> 
 (exists C , exists D, A ≡ C[←d] /\ Γ ⊢ c : Π(D),C /\ Γ ⊢ d : D).
intros.
apply (Genv_ Γ (c·d) A); trivial.
Qed.


(* Weakening / Thining Lemma *)
(* if we insert something in the context , we have to lift our judgment *)
Theorem weakening: (forall Δ t T, Δ ⊢ t : T -> forall Γ d s n Δ', ins_in_env Γ d n Δ Δ' ->   Γ ⊢ d :!s -> 
                 Δ' ⊢ t ↑ 1 # n : T ↑ 1 # n ) /\
(forall Γ, Γ ⊣ -> forall Δ Γ' n A , ins_in_env Δ A n Γ Γ' -> forall s, Δ ⊢ A : !s -> Γ' ⊣).
apply typ_induc; simpl in *; intros.
(*1*)
eauto.
(*2*)
destruct (le_gt_dec n v).
constructor. eauto. destruct i as (AA & ?& ?). exists AA; split. rewrite H2.
change (S (S v)) with (1+ S v).
rewrite liftP3; intuition. eapply ins_item_ge. apply H0. trivial. trivial.
constructor. eauto.  eapply ins_item_lift_lt. apply H0. trivial. trivial.
(*3*)
econstructor. apply r. eauto. eapply H0. constructor; apply H1. apply H2.
(*4*)
econstructor. eauto. 
eapply H0. constructor; apply H1. apply H2. 
(*5*)
change n with (0+n). rewrite substP1. simpl.
apply cApp with B↑ 1 # n.
eauto. eauto.
(*6*)
apply Cnv with (A↑ 1 # n) s; intuition.
eauto. eauto. 
(** wf **)
inversion H; subst; clear H.
apply wf_cons with s; trivial.
(**)
inversion  H0; subst; clear H0.
apply wf_cons with s0; trivial. 
apply wf_cons with s; trivial. change !s with !s ↑ 1 # n0.
eapply H.  apply H6. apply H1.
Qed.


Theorem thinning :
   forall Γ t T A s,
      Γ ⊢ t : T -> 
   Γ ⊢ A : !s ->
   A::Γ ⊢ t ↑ 1 : T ↑ 1.
intros.
destruct weakening.
eapply H1. apply H. constructor. apply H0.
Qed.

Theorem thinning_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall t T , Δ' ⊢ t : T  -> Δ ⊣ ->
               Δ ⊢ t ↑ n : T ↑ n.
intro n; induction n; intros.
inversion H; subst; clear H.
rewrite 2! lift0; trivial.
inversion H; subst; clear H.
change (S n) with (1+n).
replace (t ↑ (1+n)) with ((t ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
apply thinning with s; trivial.
eapply IHn. apply H3. trivial. eauto.
Qed.

Definition typ_subst := forall Γ t T , Γ  ⊢ t  : T  -> forall Δ P A, Δ  ⊢ P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ' ⊢ t [ n ←P ]  : T [ n ←P ].
Definition wf_subst := forall Γ ,  Γ ⊣ -> forall Δ P A n Γ' , Δ ⊢ P : A -> 
  sub_in_env  Δ P A n Γ Γ' ->     Γ' ⊣ .

Lemma sub_trunc : forall Γ0 a A n Γ Δ, sub_in_env Γ0 a A n Γ Δ -> trunc n Δ Γ0.
induction 1.
apply trunc_O.
apply trunc_S. trivial.
Qed.


Theorem substitution : typ_subst /\ wf_subst.
apply typ_induc; simpl; intros.
(*1*)
eauto.
(*2*)
destruct (lt_eq_lt_dec v n). destruct s.
constructor. eauto. eapply nth_sub_item_inf. apply H1. intuition. trivial.
destruct i as (AA & ?& ?).
subst. rewrite substP3; intuition. 
rewrite <- (nth_sub_eq H1 H4).
eapply thinning_n.
eapply sub_trunc. apply H1. trivial.  eauto.
constructor. eauto.
destruct i as (AA & ? &?). subst.  rewrite substP3; intuition.
exists AA; split. replace (S (v-1)) with v by intuition. trivial.
eapply nth_sub_sup. apply H1. intuition.
rewrite <- pred_of_minus.
rewrite <- (S_pred v n l). trivial.
(*4*)
econstructor. apply r. eauto. eapply H0. apply H1. constructor; apply H2. eauto.
(*5*)
econstructor. eauto.  eapply H0. apply H1. constructor; apply H2. eauto. 
(*6*)
rewrite subst_travers. econstructor.
replace (n+1) with (S n) by intuition. eapply H. apply H1. trivial. trivial.
eauto.  
(*7*)
econstructor.  apply Betac_subst2. apply b.
eauto. eauto.
(** wf **)
inversion H0.
inversion H1; subst; clear H1. eauto.
econstructor. eapply H. apply H0. trivial. eauto. 
Qed.


Lemma wf_item : forall Γ A n, A ↓ n ∈ Γ ->
   forall  Γ', Γ ⊣ ->  trunc (S n) Γ Γ' -> exists s, Γ' ⊢ A : !s.
induction 1; intros.
inversion H0; subst; clear H0.
inversion H5; subst; clear H5.
inversion H; subst.
exists s; trivial.
inversion H1; subst; clear H1.
inversion H0; subst.
apply IHitem; trivial. eauto. 
Qed.

Lemma wf_item_lift : forall Γ t n ,Γ ⊣  -> t ↓ n ⊂ Γ ->
  exists s,  Γ ⊢ t  : !s.
intros.
destruct H0 as (u & ? & ?).
subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
destruct (wf_item Γ u n H1 Γ' H H0) as (t &  ?).
exists t. change !t with (!t ↑(S n)).
eapply thinning_n. apply H0. trivial. trivial.
Qed.

(* if A types something, than it has to be a valid type
which is a sort, or something typed by a sort *)
Theorem TypeCorrect : forall Γ a A, Γ ⊢ a : A  -> 
 (exists s, A = !s) \/ (exists s, Γ ⊢ A : !s).
intros; induction H.
(*1*)
left; exists t; reflexivity.
(*2*)
apply wf_item_lift in H0. right; trivial. trivial.
(*4*)
eauto.
(*5*)
eauto.
(*6*)
destruct IHtyp1. destruct H1; discriminate. destruct H1 as (s & ?).
apply Geniii in H1. destruct H1 as (s1 &s2 & s3 & h); decompose [and] h; clear h.
right; exists s2.
change (!s2) with (!s2 [← b]).
destruct substitution as ( ? & _).  eapply H4. apply H5. apply H0. constructor. eauto.
(*8*)
right; exists s; trivial.
Qed.
