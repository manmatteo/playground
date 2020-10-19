Require Import dn_term.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.

Inductive Beta : Term -> Term -> Prop :=
 | Beta_head : forall  A b c,  Beta ((λ[ A ], b)· c)  ( b [← c])
 | Beta_red1 : forall x y z, Beta x  y ->Beta (x· z)  (y·z)
 | Beta_red2 : forall x y z, Beta x  y -> Beta (z·x)  (z · y)
 | Beta_lam : forall x y A , Beta x  y -> Beta (λ [A],  x)  (λ [ A], y)
 | Beta_lam2 : forall x A B , Beta A  B -> Beta (λ [ A ], x)  (λ [B ], x)
 | Beta_pi : forall x y A ,Beta  x  y -> Beta (Π (A), x)  (Π(A), y)
 | Beta_pi2 : forall x A B, Beta A  B -> Beta (Π(A), x)  (Π(B), x)
.

Notation " A → B " := (Beta A B) (at level 80) : DN_scope.

Inductive Betas : Term -> Term -> Prop :=
 | Betas_refl : forall x, Betas x x
 | Betas_Beta : forall x y, x → y -> Betas x y
 | Betas_trans : forall x y z, Betas x y -> Betas y z -> Betas x z.

Notation " A →→ B " := (Betas A B) (at level 80) : DN_scope.

Inductive Betac : Term -> Term -> Prop :=
 | Betac_Betas : forall x y, x →→ y -> Betac x y
 | Betac_sym : forall x y, Betac x y -> Betac y x
 | Betac_trans : forall x y z, Betac x y -> Betac y z -> Betac x z.

Notation " A ≡ B " := (Betac A B) (at level 80) : DN_scope.

Hint Constructors Beta : core.
Hint Constructors Betas : core.
Hint Constructors Betac : core.

(* dummy facts about Betas et Betac, mainly congruence *)
Lemma Betac_refl : forall T, T ≡ T.
intros; constructor; constructor.
Qed.

Hint Resolve Betac_refl : core.

Lemma Betas_App : forall a b c d, a →→ b -> c →→ d -> a·c →→ b·d.
assert (forall a b c, b →→ c ->  a·b →→ a·c).
induction 1; eauto.
assert (forall a b c, b→→c -> b· a →→ c· a).
induction 1; eauto.
intros; eauto.
Qed.

Hint Resolve Betas_App : core.

Lemma Betac_App : forall a b c d, a ≡ b -> c ≡ d -> a·c ≡ b·d.
assert (forall a b c, b ≡ c ->  a· b ≡ a· c).
induction 1; eauto.
assert (forall a b c , b ≡ c -> b·a ≡ c·a).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_App : core.

Lemma Betas_La : forall a b c d, a →→  b -> c →→ d -> λ[a], c →→ λ[b], d.
assert (forall a b c , a →→ b -> λ[c],  a →→ λ[c], b).
induction 1; eauto.
assert (forall a b c, a →→ b -> λ[a], c →→ λ[b], c).
induction 1; eauto.
eauto.
Qed.


Hint Resolve Betas_La : core.

Lemma Betac_La: forall a b c d, a ≡ b -> c ≡ d -> λ[a],c ≡ λ[b], d.
assert (forall a b c, a ≡ b -> λ[c], a ≡ λ[c], b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> λ[a], c ≡ λ[b], c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_La : core.

Lemma Betas_Pi : forall a b c d, a →→ b -> c →→ d -> Π(a), c →→ Π(b), d.
assert (forall a b c , a →→ b -> Π (c), a →→ Π(c), b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Π(a), c →→ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betas_Pi : core.

Lemma Betac_Pi : forall a b c d, a ≡ b -> c ≡ d -> Π(a), c ≡ Π(b), d.
assert (forall a b c , a ≡ b -> Π(c), a ≡ Π(c), b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> Π(a), c ≡ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_Pi : core.


(* some other facts, not every thing is used in the main development *)
Lemma Beta_beta : forall a b c n,  a → b ->  a[n←c] → b[n←c] .
intros.
generalize n.
induction H; intros; simpl; intuition.
rewrite (subst_travers).
replace (n0+1) with (S n0) by intuition.
constructor.
Qed.

Lemma Betas_V : forall v t, #v →→ t -> t = #v.
intros. remember #v as V; induction H; trivial.
subst; inversion H.
transitivity y. apply IHBetas2. rewrite <- HeqV; intuition. intuition.
Qed.


Lemma Betas_S : forall s t, !s →→ t -> t = !s.
intros. remember !s as S; induction H; trivial.
subst; inversion H.
transitivity y. apply IHBetas2. rewrite <- HeqS; intuition. intuition.
Qed.


Lemma Betas_Pi_inv : forall A B t, Π(A), B →→ t -> 
  exists C, exists D, t = Π(C), D /\ A →→ C /\ B →→ D.
intros.
remember (Π(A), B) as P. revert A B HeqP; induction H; intros; subst; eauto.
inversion H; subst; clear H.
exists A; exists y0; intuition.
exists B0; exists B; intuition.
destruct (IHBetas1 A B) as (C' & D' & ?); intuition.
destruct (IHBetas2 C' D') as (C'' & D'' &?); intuition.
exists C''; exists D''; eauto.
Qed.

Lemma Betas_La_inv : forall A B t, λ[A], B →→ t -> 
  exists C, exists D, t = λ[C], D /\ A →→ C /\ B →→ D.
intros.
remember (λ[A], B) as P. revert A B HeqP; induction H; intros; subst; eauto.
inversion H; subst; clear H.
exists A; exists y0; intuition.
exists B0; exists B; intuition.
destruct (IHBetas1 A B) as (C' & D' & ?); intuition.
destruct (IHBetas2 C' D') as (C'' & D'' &?); intuition.
exists C''; exists D''; eauto.
Qed.


(* Beta Betas and Betac are correct related to lift / subst of DeBruijn index *)
Lemma Beta_lift: forall a b n m, a → b -> a ↑ n # m → b ↑ n # m .
intros.
generalize n m; clear n m.
induction H; intros; simpl; eauto.
change m with (0+m).
rewrite substP1.
constructor.
Qed.


Lemma Betas_lift : forall a b n m , a →→ b -> a ↑ n # m →→ b ↑ n # m .
intros.
induction H.
constructor.
constructor; apply Beta_lift; intuition.
apply Betas_trans with (y:= y ↑ n # m ); intuition.
Qed.


Lemma Betac_lift : forall a b n m, a ≡ b -> a ↑ n # m ≡ b ↑ n # m .
intros.
induction H.
constructor.
apply Betas_lift; trivial.
apply Betac_sym; trivial.
apply Betac_trans with (y:=y ↑ n # m); trivial.
Qed.

Hint Resolve Beta_lift Betas_lift Betac_lift : core.


Lemma Betas_subst : forall c a b n, a →→ b -> c [n←a] →→ c[n← b]. 
induction c; intros; simpl; eauto.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Hint Resolve Betas_subst : core.

Lemma Betas_subst2 : forall c a b n, a →→ b -> a [n← c] →→ b [n ← c].
induction 1; eauto.
constructor. apply Beta_beta; intuition.
Qed.

Hint Resolve Betas_subst2 : core.

Lemma Betac_subst : forall c a b n, a ≡ b -> c[n←a] ≡ c [n←b].
induction c; simpl; intros; intuition.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Lemma Betac_subst2 : forall c a b n, 
  a ≡ b -> a[n←c] ≡ b[n← c] .
induction 1; eauto.
Qed.

Hint Resolve Betac_subst Betac_subst2 : core.

(* Beta parallel definition *)
Inductive Betap : Term -> Term -> Prop :=
 | Betap_refl : forall m, Betap m m
 | Betap_lam: forall m m' A A', Betap m m' ->Betap A A'-> 
    Betap (λ [ A], m) (λ[ A'], m')
 | Betap_pi: forall m m' A A', Betap m m' -> Betap A A' -> 
    Betap (Π(A), m) (Π(A'), m')
 | Betap_App : forall m m' n n', Betap m m' -> Betap n n' -> 
    Betap (m·n) (m'·n')
 | Betap_head : forall m m' n n' A, Betap m m' -> Betap n n' -> 
    Betap((λ[A], m)· n) (m'[← n']).

Notation "m →' n" := (Betap m n) (at level 80) : DN_scope.

Local Hint Constructors Betap : core.

Lemma Betap_lift: forall a b n m, a →' b -> a ↑ n # m →' b ↑ n # m .
intros.
revert n m.
induction H; simpl; intuition.
change m0 with (0+m0).
rewrite substP1.
constructor; intuition.
Qed.

Local Hint Resolve Betap_lift : core.

(* inversion lemmas for beta // *)
Lemma Betap1:forall m m' n n' x, 
  m →' m'  -> n →' n' -> m[x←n] →' m'[x←n'].
intros.
revert x.
induction H; simpl; intuition.
(* 1/5 *)
revert x; induction m;intros;  simpl; intuition.
destruct (lt_eq_lt_dec v x); intuition.
rewrite subst_travers. replace (S x) with (x+1) by intuition. constructor; intuition.
Qed.


(* Beta // has the diamond property *)
Lemma Betap_diamond : forall m m1 m2 ,
   m →' m1 -> m →' m2 -> (exists m3, m1 →' m3 /\ m2 →' m3). 
intros.
revert m2 H0. 
induction H; intros.
(*1/5*)
exists m2; intuition.
(*2/5*)
inversion H1; subst; clear H1.
exists (λ[A'], m'); intuition. 
destruct (IHBetap1 m'0 H4) as (b & ? & ?).
destruct (IHBetap2 A'0 H6) as (D & ?& ?).
exists (λ[D], b); intuition. 
(*3/5*)
inversion H1; subst; clear H1.
exists (Π(A'), m'); intuition. 
destruct (IHBetap1 m'0 H4) as (B'' & ? & ?).
destruct (IHBetap2 A'0 H6) as (A'' & ?& ?).
exists (Π(A''), B''); intuition. 
(*4/5*)
inversion H1; subst; clear H1.
exists (m' · n'); intuition.
destruct (IHBetap1 m'0 H4) as (u & ?& ?).
destruct (IHBetap2 n'0 H6) as (v & ?& ?).
exists (u · v); intuition.
inversion H; subst; clear H.
destruct (IHBetap2 n'0 H6) as (n'' & ?& ?).
exists ( m'0 [ ← n'']); intuition. apply Betap1; trivial.
destruct (IHBetap2 n'0 H6) as (n'' & ?& ?).
destruct (IHBetap1 (λ[A],m'0)) as  (L & ?& ?); intuition.
inversion H2; subst; clear H2; inversion H5; subst; clear H5.
exists ( m'1 [ ← n'']); intuition. apply Betap1; trivial.
exists ( m'1 [ ← n'']); intuition. apply Betap1; trivial.
exists ( m' [ ← n'']); intuition. apply Betap1; trivial.
exists ( m' [ ← n'']); intuition. apply Betap1; trivial.
(*5/5*)
inversion H1; subst; clear H1.
exists (m'[← n']); intuition.
destruct (IHBetap2 n'0 H6) as (n'' & ?& ?).
inversion H4; subst; clear H4.
exists (m'[← n'']); intuition. apply Betap1; trivial. 
destruct (IHBetap1 m'1 H7) as (m'' & ?& ?).
exists (m''[← n'']); intuition. apply Betap1; trivial.
destruct (IHBetap2 n'0 H7) as (n'' & ?& ?).
destruct (IHBetap1 m'0 H6) as (m'' & ?& ?).
exists (m''[← n'']); intuition. apply Betap1; trivial. apply Betap1; trivial.
Qed.



Inductive Betaps : Term -> Term -> Prop :=
 | Betaps_refl : forall x , Betaps  x x
 | Betaps_trans : forall x y z  , Betap x y -> Betaps y z -> Betaps x z
.


Notation " x  →→' y " := (Betaps x y) (at level 80) : DN_scope.

Local Hint Constructors Betaps : core.

(* the closure of Beta is the same as Beta // *)

Lemma Betas_Betap_closure : forall x y , x →' y -> x →→ y.
induction 1; eauto.
Qed.

Local Hint Resolve Betas_Betap_closure : core.


Lemma Betas_Betaps_closure : forall x y , 
  x →→'  y -> x →→  y.
induction 1; eauto.
Qed.

Lemma Betap_Beta_closure : forall x y,
 x → y -> x →' y.
induction 1; intuition.
Qed.

Local Hint Resolve Betas_Betaps_closure Betap_Beta_closure : core.

Lemma Betaps_Beta_closure :forall x y, x → y -> x →→' y.
eauto.
Qed.

Local Hint Resolve Betaps_Beta_closure : core.

Lemma Betaps_trans2 : forall x y z , x →→' y -> y →→' z  -> x →→' z.
intros. revert z H0; induction H; eauto.
Qed.

Local Hint Resolve Betaps_trans2 : core.

Lemma Betaps_Betas_closure : forall x y , x →→ y -> x →→' y.
induction 1; eauto.
Qed.

Local Hint Resolve Betaps_Betas_closure : core.

Lemma sub_diamond_Betaps : 
(   forall x y z, x →' y -> x →' z -> (exists t, y →' t /\ z →' t) )
 -> forall x y z , x →' y -> x →→' z ->(exists t, y →→' t /\ z →' t).
intros.
revert y H0. induction H1; eauto. 
intros.
destruct (H x y y0 H0 H2) as (x1 & ?& ?).
destruct (IHBetaps x1 H3) as (x2 & ? & ?).
exists x2; eauto.
Qed.



Lemma diamond_Betaps : 
(   forall x y z, x →' y -> x →' z -> (exists t, y →' t /\ z →' t) )
 ->
  forall  x y z, x →→' y -> x →→' z -> (exists t,y →→' t /\ z →→' t) .
intros. 
revert z H1.
induction H0; intros; eauto.
destruct (sub_diamond_Betaps H x y z0 H0 H2) as (Z & ? & ?).
destruct (IHBetaps Z H3) as (ZZ & ?& ?). 
exists ZZ;eauto.
Qed.


(* from all this => Beta* is confluent \o/
 a hand written proof is in Barendregt *)
Lemma Betas_diamond: 
  forall x y z, x →→ y -> x →→ z -> (exists t, y →→ t /\ z →→ t).
intros.
destruct (diamond_Betaps Betap_diamond x y z); intuition.
exists x0; intuition.
Qed.

(* facts about confluency & church rosser *)

Lemma Betac_confl : forall x y, x ≡ y -> (exists z, x →→ z /\ y →→ z).
induction 1; eauto. destruct IHBetac as (z & ? &? ); eauto.
destruct IHBetac1 as (z1 & ? &? ); destruct IHBetac2 as (z2 & ? & ?).
destruct (Betas_diamond y z1 z2 H2 H3) as (zz & ?& ?).
exists zz; eauto.
Qed.

Lemma conv_sort : forall s t, !s ≡ !t -> s = t.
intros.
apply Betac_confl in H. destruct H as (z & ?& ?).
apply Betas_S in H.
apply Betas_S in H0.
rewrite H in H0.
injection H0; trivial.
Qed.

Lemma conv_to_sort : forall s T, !s ≡ T ->  T →→ !s.
intros.
apply Betac_confl in H.
destruct H as (z & ?& ?). 
apply Betas_S in H.
subst. trivial.
Qed.

Lemma conv_to_var : forall v T , #v ≡ T -> T →→ #v.
intros.
apply Betac_confl in H.
destruct H as (z & ?& ?).
apply Betas_V in H.
subst; trivial.
Qed.


Lemma Betac_V : forall s t, #s ≡ #t -> s = t.
intros.
apply conv_to_var in H.
apply Betas_V in H.
injection H; trivial.
Qed.

(* Pi is injective *)
Lemma Betac_Pi_inv : forall A B C D, Π(A), B ≡ Π(C), D ->
 A ≡ C /\ B ≡ D.
intros.
apply Betac_confl in H. destruct H as (z & ? & ?).
apply Betas_Pi_inv in H.
apply Betas_Pi_inv in H0.
destruct H as (c1 & d1 & ? & ? & ?). 
destruct H0 as (c2 & d2 & ? & ?& ?).
rewrite H0 in H; injection H; intros; subst; split; eauto.
Qed.
