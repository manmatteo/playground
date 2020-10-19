Require Import dn_term.
Require Import dn_red.
Require Import dn_context.
Require Import dn_typ.
Require Import List.

(* How to deal with Beta reduction in the context *)
Inductive Beta_env : Env -> Env -> Prop :=
 | Beta_env_hd : forall A B e, A → B -> Beta_env (A::e) (B::e)
 | Beta_env_cons : forall A e f, Beta_env e f -> Beta_env (A::e) (A::f)
.

Inductive Betas_env : Env -> Env -> Prop :=
 | Betas_env_refl : forall e, Betas_env e e
 | Betas_env_Beta : forall e f, Beta_env e f -> Betas_env e f
 | Betas_env_trans : forall e f g, Betas_env e f -> Betas_env f g -> Betas_env e g.

Hint Constructors Beta_env Betas_env.

Notation " a →e b " := (Beta_env a b) (at level 20) : DN_scope.
Notation " a →→e b " := (Betas_env a b) (at level 20) : DN_scope.

(* simples facts on env / beta *)
Lemma Betas_env_nil_ : forall e g,e →→e g -> (e = nil -> g = nil).
intros e g H.
induction H; intros.
trivial.
subst.
inversion H.
intuition.
Qed.

Lemma Betas_env_nil : forall g, nil →→e g -> g = nil.
intros.
apply (Betas_env_nil_ nil g H); intuition.
Qed.

Lemma Betas_env_nil2_ : forall e g , e →→e g -> (g = nil -> e = nil).
intros e g H; induction H; intros.
trivial.
subst; inversion H.
intuition.
Qed.

Lemma Betas_env_nil2 : forall e, e →→e nil -> e = nil.
intros ; apply (Betas_env_nil2_ e nil) ; trivial.
Qed.

Lemma Betas_env_inv_ : forall E F, E →→e F -> 
 (forall a b g f,E = a::g -> F = b::f  -> a→→b /\ g→→e f).
intros E F H; induction H; intros.
rewrite H0 in H.
injection H; intros; subst.
split; constructor.
inversion H; subst.
injection H3; injection H4; intros; subst.
rewrite H5; split; constructor; trivial.
injection H3; injection H4; intros; subst.
rewrite H6; split; constructor; trivial.
destruct f.
rewrite (Betas_env_nil g H0) in *; discriminate.
subst.
destruct (IHBetas_env2 t b f f0); intuition; 
destruct (IHBetas_env1 a t g0 f); intuition.
apply Betas_trans with (y:=t); trivial.
apply Betas_env_trans with  (f:=f); trivial.
Qed.

Lemma Betas_env_inv :forall a b g f, (a::g)  →→e  (b::f) -> a →→ b /\ g→→e f.
intros.
apply Betas_env_inv_ with (a::g) (b::f) ; trivial.
Qed.

Lemma Betas_env_hd : forall A C f, A→→C -> (A::f) →→e (C::f).
intros.
induction H.
constructor.
constructor; apply Beta_env_hd; trivial.
apply Betas_env_trans with (f:=y::f); intuition.
Qed.

Lemma Betas_env_cons : forall A g f , g →→e f -> (A::g) →→e (A::f).
intros.
induction H.
constructor.
constructor; apply Beta_env_cons; trivial.
apply Betas_env_trans with (f:=A::f); trivial.
Qed.

Lemma Betas_env_comp : forall A B g f, A→→B -> g→→e f -> (A::g) →→e (B::f).
intros.
apply Betas_env_trans with (f:= A::f).
apply Betas_env_cons; trivial.
apply Betas_env_hd; trivial.
Qed.


(* Important one 
we have to proof subject reduction and context reduction at the same time
*)

Lemma Beta_env_sound :   forall Γ x A, Γ ⊢ x : A-> forall Γ', Γ' ⊣ -> Γ →e Γ' -> Γ' ⊢ x : A  .
induction 1; intros.
(**)
constructor; trivial.
(**)
generalize dependent A. revert H1 H v. 
induction H2; intros. destruct H2 as (AA&  ? & ?). inversion H3; subst; clear H3.
inversion H1; subst; clear H1. inversion H0; subst; clear H0.
apply Cnv with (B↑ 1) s0. eauto.
constructor. eauto.  exists B; intuition.
change !s0 with !s0 ↑ 1. apply thinning with s ;trivial.
constructor. eauto. exists AA; intuition.
destruct H0 as (AA&  ? & ?).  inversion H3; subst; clear H3.
constructor. trivial. exists A; intuition.
change (S(S n)) with (1+S n). change #(S n) with (#n  ↑ 1).
rewrite <- lift_lift.
inversion H1; subst; clear H1.
apply thinning with s; trivial. apply IHBeta_env. eauto. inversion H; subst; clear H. eauto. 
exists AA; intuition.

econstructor; eauto.
econstructor. eauto. apply IHtyp2.
destruct (Geniii Γ' A B !s)as (s1 &s2 & s3 & h); intuition.
apply wf_cons with s1; trivial. 

eauto. eauto. eauto.
Qed.

Lemma Beta_sound : forall Γ x A, Γ ⊢ x : A-> forall y, x→ y ->  Γ ⊢y : A.
induction 1; intros.
(*1*)
inversion H1.
(*2*)
inversion H1.
(*3*)
inversion H2; subst; clear H2. econstructor; eauto. econstructor. apply H. intuition.
eapply Beta_env_sound. apply H1. eauto. intuition.
(*4*)
inversion H1; subst; clear H1. eauto.
apply Cnv with ( Π (B0), B) s. eauto.
assert (Γ ⊢ Π (B0), B : !s) by intuition.
econstructor. apply H1. eapply Beta_env_sound. apply H0.
apply Geniii in H1. destruct H1 as (s1 & s2 & s3 & ?); intuition. eauto.
eauto. trivial.
(*5*)
(* Proof from Barendregt 92 *)
(*
 Γ ⊢ a : Π(B), A -> Γ ⊢ Π(B), A : !s  ( Π(B), A is welltyped Γ)
*)
assert (exists s, Γ ⊢ Π(B), A : !s).
   apply TypeCorrect in H; destruct H.  destruct H; discriminate. trivial.
   destruct H2 as (u & ?).
(* 
  Γ ⊢ Π(B), A : !s  ->  Γ ⊢ B : !s1      B::Γ ⊢ A: s2    Rel s1 s2 s
  Π(B), A  is well formed so we can type his domain / co domain
*)
assert (exists s1 , exists s2, Rel s1 s2 u /\ Γ ⊢ B : !s1 /\ B::Γ ⊢ A : !s2).
   apply Geniii in H2. destruct H2 as (s1 & s2 & s3 & h); decompose [and] h; clear h. 
   apply conv_sort in H2. subst. exists s1; exists s2; intuition.
   destruct H3 as (s1 & s2 & s3 & ? & ? ).
(* 
   Γ ⊢ b : B     B::Γ ⊢ A : !t    -> Γ ⊢ A[ ← b] : !t
*)
assert (Γ ⊢ A[ ← b] : !s2).
   change !s2 with !s2[←b]. destruct substitution as ( ? & _).
   apply H5 with (B::Γ)  Γ B  ; intuition. eauto. 
inversion H1; subst; clear H1.
(* case (λ(x:A0) . b0) b  →  b[b0] *)
(*
  Γ ⊢ λ[A0], b0 : Π (B),A ->  A0 == B     and A0::Γ ⊢ b0 : D  with D == A
*)
apply Geniv in H. destruct H as (s1' &s2' &s3' & D & h); decompose [and] h; clear h.
apply Betac_Pi_inv in H. destruct H.
(* since A == D, convert the type *)
apply Cnv with (D [ ← b]) s2; intuition.
(* apply the substitution lemma with everthing we have now *)
destruct substitution as ( ?  &_).
apply H10 with (A0::Γ) Γ A0 ; intuition.
(* convert since A0 == B *)
apply Cnv with B s1'; intuition. eauto.
(* case a b →  a' b  or a b  → a b'  with  a → a' or  b → b' *)
eauto. 
apply Cnv with A [ ← y0] s2; intuition.
econstructor. apply H ; intuition.
destruct substitution as(  ? & _). intuition.
(**)
eauto.
Qed.


Lemma SubjectRed : forall Γ x T, Γ ⊢ x : T-> 
  forall y , x →→ y -> Γ ⊢ y : T.
intros. induction H0.
trivial. eapply Beta_sound.
apply H. trivial. intuition.
Qed.

(* Type reduction *)
Lemma Betas_typ_sound : forall Γ x T, Γ ⊢ x : T -> 
 forall T', T →→ T' -> Γ ⊢ x : T'.
intros.
assert ((exists s, T = !s )\/ exists s,  Γ ⊢ T : !s ) by ( apply TypeCorrect in H; intuition).
destruct H1 as [[s Hs]|[s Hs]].
rewrite Hs in *. apply Betas_S in H0. rewrite H0; trivial.
apply Cnv with T s; intuition.
apply SubjectRed with T; intuition.
Qed.

Lemma Beta_env_sound2 : forall Γ Γ', Γ ⊣ -> Γ →e Γ' -> Γ' ⊣.
intros. induction H0; intuition.
apply wf_inv in H. destruct H as (s & ? ).
econstructor. eapply Beta_sound. apply H. trivial.
inversion H; subst; clear H.
econstructor. eapply Beta_env_sound. apply H2.  apply IHBeta_env.
eauto. trivial.
Qed.

Lemma Betas_env_sound2 : forall Γ Γ', Γ ⊣ -> Γ →→e Γ' -> Γ' ⊣.
intros.
induction H0; intuition.
eapply Beta_env_sound2. apply H. trivial.
Qed.

Lemma Betas_env_sound :   forall Γ x A, Γ ⊢ x : A-> forall Γ', Γ' ⊣ -> Γ →→e Γ' -> Γ' ⊢ x : A  .
intros.
induction H1; intuition.
eapply Beta_env_sound. apply H. trivial. trivial.
apply IHBetas_env2. apply H1.
eapply Betas_env_sound2. eapply wf_typ. apply H. trivial. trivial.
Qed.




(* compilation of all this *)
Lemma Subject_Reduction :  forall Γ x A, Γ ⊢ x : A ->
  forall Γ' y B, x→→ y -> Γ →→e Γ' -> A→→ B -> Γ' ⊢ y : B.
intros.
apply Betas_typ_sound with A; intuition.
apply Betas_env_sound with Γ; intuition.
apply SubjectRed with x; intuition.
eapply Betas_env_sound2. eapply wf_typ. apply H. trivial.
Qed.

