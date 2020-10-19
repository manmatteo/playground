Require Import dn_term.
Require Import dn_red.
Require Import sc_term. 
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.

Open Scope SC_scope.

Fixpoint append l l' {struct l} := match l with
 | [[]] => l'
 | u ::: k => u ::: (append k l')
end.

Notation "l @ l'" := (append l l') (at level 5, left associativity) : SC_scope.

Lemma append_lift : forall l1 l2 n m , (l1 @ l2) ↑↑ n # m = (l1 ↑↑ n # m) @ (l2 ↑↑ n # m).
induction l1; intros; simpl.
trivial.
rewrite IHl1. trivial.
Qed.

Lemma append_subst: forall l1 l2 x n , (l1 @ l2 [[x ← n]]) = (l1 [[x ← n]])@( l2 [[x ← n]]).
induction l1; intros; simpl; intuition.
rewrite IHl1. trivial.
Qed.

Lemma append_nil : forall l , l@[[]] = l.
induction l;simpl;trivial.
rewrite IHl. trivial.
Qed.

Lemma append_assoc : forall l1 l2 l3, l1 @ (l2 @ l3) = (l1 @ l2) @ l3.
induction l1; intros.
simpl; trivial.
simpl. rewrite IHl1; trivial.
Qed.


Lemma append_assoc1 : forall l1 M l2, l1@(M:::l2) = (l1@(M:::[[]]))@l2.
induction l1; simpl; intros.
trivial.
rewrite IHl1. trivial.
Qed.

Reserved Notation " s → t" (at level 80,  no associativity) .
Reserved Notation " l →' g" (at level 80,  no associativity).


Inductive Rx : Term -> Term -> Prop :=
  | Bnil : forall t , (t · [[]]) → t
  | Cvar : forall x l l', ( (x ## l) · l' ) → (x ##(l@l'))
  | Cterm : forall t l l', (( t · l) · l') → (t · (l@l'))
  | R_La1 : forall A s t, s → t -> λ[A],s → λ[A],t
  | R_La2 : forall A B s, A → B -> λ[A],s → λ[B],s
  | R_App : forall s t l, s → t -> s · l → t · l
  | R_App2 : forall l l' s, l →' l' -> s · l → s · l'
  | R_App3 : forall l l' x, l →' l' -> x ## l → x ## l'
  | R_Pi1 : forall A B D, B → D -> Π(A),B → Π(A),D
  | R_Pi2 : forall A B C, A → C -> Π(A),B → Π(C),B
where "s → t" := (Rx s t) : SC_scope
with Rx_list : Term_List -> Term_List -> Prop :=
  | R_hd : forall t t' l, t → t' -> t ::: l →' t' ::: l
  | R_tl : forall t l l', l →' l' -> t ::: l →' t ::: l'
where "l →' g" := (Rx_list l g) : SC_scope.

Reserved Notation " s ▹ t" (at level 80,  no associativity).
Reserved Notation " l ▹' g" (at level 80,  no associativity).

Inductive RBx : Term -> Term -> Prop :=
  | Bcons': forall A u v l, ((λ[A],u) · (v ::: l)) ▹ ((u [ ← v]) · l)
  | Bnil' : forall t , (t · [[]]) ▹ t
  | Cvar' : forall x l l', ( (x ## l) · l' ) ▹ (x ## (l@l'))
  | Cterm' : forall t l l', (( t · l) · l') ▹ (t · (l@l'))
  | R_La1' : forall A s t, s ▹ t -> λ[A],s ▹ λ[A],t
  | R_La2' : forall A B s, A ▹ B -> λ[A],s ▹ λ[B],s
  | R_App' : forall s t l, s ▹ t -> s · l ▹ t · l
  | R_App2' : forall l l' s, l ▹' l' -> s · l ▹ s · l'
  | R_App3' : forall l l' x, l ▹' l' -> x ## l ▹ x ## l'
  | R_Pi1' : forall A B D, B ▹ D -> Π(A),B ▹ Π(A),D
  | R_Pi2' : forall A B C, A ▹ C -> Π(A),B ▹ Π(C),B
where "s ▹ t" := (RBx s t) : SC_scope
with RBx_list : Term_List -> Term_List -> Prop :=
  | R_hd' : forall t t' l, t ▹ t' -> t ::: l ▹' t' ::: l
  | R_tl' : forall t l l', l ▹' l' -> t ::: l ▹' t ::: l'
where "l ▹' g" := (RBx_list l g) : SC_scope.

Hint Constructors Rx Rx_list RBx RBx_list.

Fixpoint DN_to_SC (t:dn_term.Term) {struct t} : Term := match t with 
  | (!s)%DN => !s
  | (# x)%DN  =>  x ## [[]]
  | (u · v)%DN =>  DN_to_SC_List ((DN_to_SC v):::[[]]) u
  | (Π(A), B)%DN => Π (DN_to_SC A ), (DN_to_SC B )
  | (λ[A],b)%DN => λ [DN_to_SC A ], (DN_to_SC b) 
 end
with DN_to_SC_List (l : Term_List) (t : dn_term.Term) {struct t} : Term := match t with
  | (# x)%DN  =>  x ## l 
  | (u · v)%DN => DN_to_SC_List ((DN_to_SC v):::l) u
  | (!s)%DN => !s · l
  | (Π(A),B)%DN => (Π (DN_to_SC A ), (DN_to_SC B )) · l
  | (λ[A],b)%DN => (λ [DN_to_SC A ], (DN_to_SC b) ) · l
 end.

Fixpoint SC_to_DN (t:Term) {struct t} : dn_term.Term := match t with 
  | Π(A),B => (Π(SC_to_DN A),(SC_to_DN B))%DN
  | λ[A],b => (λ[SC_to_DN A],(SC_to_DN b))%DN
  | !s => (!s)%DN
  | x ## l => SC_to_DN_List ((#x)%DN) l
  | m · l => SC_to_DN_List (SC_to_DN m) l
 end
with SC_to_DN_List (z:dn_term.Term) (l:Term_List) {struct l} : dn_term.Term := match l with
  | [[]] => z
  | t ::: q => SC_to_DN_List (z · (SC_to_DN t))%DN q
end.


Lemma DN_to_SC_lift : forall t n m , (DN_to_SC (t ↑ n # m)%DN ) = (DN_to_SC t) ↑ n # m 
 with DN_to_SC_List_lift : forall t l n m, (DN_to_SC_List (l↑↑n # m) (t ↑ n # m)%DN) = (DN_to_SC_List l t) ↑ n # m.
induction t; simpl; intros.
destruct (le_gt_dec m v). simpl. trivial.
simpl. trivial.

trivial.

rewrite IHt2. rewrite <- DN_to_SC_List_lift.
f_equal.

rewrite IHt1. rewrite IHt2. trivial.

rewrite IHt1. rewrite IHt2. trivial.

induction t; simpl; intros.
destruct (le_gt_dec m v). simpl. trivial.
simpl. trivial.

trivial.

rewrite <- IHt1.  rewrite DN_to_SC_lift. f_equal.

rewrite DN_to_SC_lift. rewrite DN_to_SC_lift. trivial.

rewrite DN_to_SC_lift. rewrite DN_to_SC_lift. trivial.
Qed.

Fixpoint xNTerm (t:Term) {struct t} : Prop := match t with 
 | x ## l => xNTerm_List l
 | ! s => True
 | Π(A),B => xNTerm A /\ xNTerm B
 | λ[A],b => xNTerm A /\ xNTerm b
 | M · l => match M with 
   | ! s => True 
   | Π(A),B => xNTerm A /\ xNTerm B 
   | λ[A],b => xNTerm A /\ xNTerm b 
   | _ => False
  end /\ xNTerm_List l /\ (~ l = [[]])
 end
with xNTerm_List (l:Term_List) {struct l} : Prop := match l with
 | [[]] => True
 | t :::q => xNTerm t /\ xNTerm_List q
end.

(* Pas sur que tout soit necessaire, mais au moins c'est la *)
Reserved Notation " s →→ t" (at level 80,  no associativity).
Reserved Notation " l →→' g" (at level 80,  no associativity).

Inductive Rx_RT : Term -> Term -> Prop :=
  | Rx_RT_refl : forall s, s →→ s
  | Rx_RT_trans : forall s t u , s → t -> t →→ u -> s →→ u
where "s →→ t" := (Rx_RT s t) : SC_scope.

Inductive Rx_RT_List : Term_List -> Term_List -> Prop :=
  | Rx_RT_List_refl : forall l , l →→' l
  | Rx_RT_List_trans : forall l l' l'' , l →' l' -> l' →→' l'' -> l →→' l''
where "l →→' g" := (Rx_RT_List l g) : SC_scope.

Hint Constructors Rx_RT Rx_RT_List.

Lemma Rx_RT_trans2 : forall s t u, s →→ t -> t →→ u -> s →→ u.
intros s t u H; generalize u; clear u; induction H; intros; intuition.
apply Rx_RT_trans with t; trivial.
apply IHRx_RT; trivial.
Qed.

Lemma Rx_RT_List_trans2 : forall j k l , j →→' k -> k →→' l -> j →→' l.
intros j k l H; generalize l; clear l; induction H; intros; intuition.
apply Rx_RT_List_trans with l'; trivial.
apply IHRx_RT_List; trivial.
Qed.

Hint Resolve Rx_RT_trans2 Rx_RT_List_trans2.

Lemma Rx_RT_onestep : forall i j , i → j -> i →→ j.
intros.
apply Rx_RT_trans with j; trivial. 
Qed.

Lemma Rx_RT_List_onestep : forall i j , i →' j -> i →→' j.
intros.
apply Rx_RT_List_trans with j; trivial.
Qed.

Hint Resolve Rx_RT_onestep Rx_RT_List_onestep.

Reserved Notation " s ▹▹ t" (at level 80,  no associativity).
Reserved Notation " l ▹▹' g" (at level 80,  no associativity).

Inductive RBx_RT : Term -> Term -> Prop :=
  | RBx_RT_refl : forall s, s ▹▹ s
  | RBx_RT_trans : forall s t u , s ▹ t -> t ▹▹ u -> s ▹▹ u
where "s ▹▹ t" := (RBx_RT s t) : SC_scope.

Inductive RBx_RT_List : Term_List -> Term_List -> Prop :=
  | RBx_RT_List_refl : forall l , l ▹▹' l
  | RBx_RT_List_trans : forall l l' l'' , l ▹' l' -> l' ▹▹' l'' -> l ▹▹' l''
where "l ▹▹' g" := (RBx_RT_List l g) : SC_scope.

Hint Constructors RBx_RT RBx_RT_List.

Lemma RBx_RT_trans2 : forall s t u, s ▹▹ t -> t ▹▹ u -> s ▹▹ u.
intros s t u H; generalize u; clear u; induction H; intros; intuition.
apply RBx_RT_trans with t; trivial.
apply IHRBx_RT; trivial.
Qed.

Lemma RBx_RT_List_trans2 : forall j k l , j ▹▹' k -> k ▹▹' l -> j ▹▹' l.
intros j k l H; generalize l; clear l; induction H; intros; intuition.
apply RBx_RT_List_trans with l'; trivial.
apply IHRBx_RT_List; trivial.
Qed.


Lemma RBx_RT_onestep : forall i j , i ▹ j -> i ▹▹ j.
intros.
apply RBx_RT_trans with j; trivial.
Qed.

Lemma RBx_RT_List_onestep : forall i j , i ▹' j -> i ▹▹' j.
intros.
apply RBx_RT_List_trans with j; trivial.
Qed.

Hint Resolve RBx_RT_trans2 RBx_RT_onestep RBx_RT_List_trans2 RBx_RT_onestep.

Lemma Rx_RT_La : forall A B s t, A →→ B -> s →→ t -> λ[A],s →→ λ[B],t.
assert (forall A B s , A →→ B -> λ[A],s →→ λ[B],s).
induction 1; eauto.
assert (forall A s t, s →→ t -> λ[A],s →→ λ[A],t).
induction 1; eauto.
eauto.
Qed.

Lemma Rx_RT_Pi : forall A B C D, A →→ B -> C →→ D -> Π(A),C →→ Π(B),D.
assert (forall A B C , A →→ B -> Π(A),C →→ Π(B),C).
induction 1; eauto.
assert (forall A C D, C →→ D -> Π(A),C →→ Π(A),D).
induction 1; eauto.
eauto.
Qed.

Lemma Rx_RT_App : forall t t' l l', t →→ t' -> l →→' l' -> (t ·l) →→ (t'· l').
assert (forall t t' l , t →→ t' -> (t ·l) →→ (t'· l)).
induction 1; eauto.
assert (forall t l l' , l →→' l' -> (t ·l) →→ (t· l')).
induction 1; eauto.
eauto.
Qed.

Lemma Rx_RT_Var : forall x l l', l →→' l' -> x ## l →→ x ## l'.
induction 1; eauto.
Qed.

Lemma Rx_RT_CVar  : forall x l1 l2 l1' l2', l1 →→' l1' -> l2 →→'  l2' -> 
  x ## l1 · l2  →→   x ## (l1'@l2').
intros.
eapply Rx_RT_trans2. apply Rx_RT_App. apply Rx_RT_Var. apply H.
apply H0.
apply Rx_RT_onestep. constructor.
Qed.

Lemma Rx_RT_CTerm  : forall t t' l1 l2 l1' l2', l1 →→' l1' -> l2 →→'  l2' -> 
  t →→ t' ->
  t · l1 · l2  →→   t' · (l1'@l2').
intros.
eapply Rx_RT_trans2. apply Rx_RT_App. apply Rx_RT_App. apply H1.
apply H. apply H0.
apply Rx_RT_onestep. constructor.
Qed.

Lemma Rx_RT_cons : forall t t' l l' , t →→ t' -> l →→' l' ->
  t ::: l →→' t' ::: l'.
assert (forall t t' l , t →→  t' ->
  t ::: l →→' t' ::: l).
induction 1; eauto. 
assert (forall t  l l', l →→' l' ->
  t ::: l →→' t ::: l').
induction 1; eauto.
eauto.
Qed.


Hint Resolve Rx_RT_La Rx_RT_Pi Rx_RT_App Rx_RT_Var Rx_RT_CVar Rx_RT_CTerm Rx_RT_cons.

Lemma RBx_RT_Var : forall x l l', l ▹▹' l' -> x ## l ▹▹ x ## l'.
induction 1; eauto.
Qed.


Lemma RBx_RT_La : forall A B s t, A ▹▹ B -> s ▹▹ t -> λ[A],s ▹▹ λ[B],t.
assert (forall A B s , A ▹▹ B -> λ[A],s ▹▹ λ[B],s).
induction 1; eauto.
assert (forall A s t, s ▹▹ t -> λ[A],s ▹▹ λ[A],t).
induction 1; eauto.
eauto.
Qed.

Lemma RBx_RT_Pi : forall A B C D, A ▹▹ B -> C ▹▹ D -> Π(A),C ▹▹ Π(B),D.
assert (forall A B C , A ▹▹ B -> Π(A),C ▹▹ Π(B),C).
induction 1; eauto.
assert (forall A C D, C ▹▹ D -> Π(A),C ▹▹ Π(A),D).
induction 1; eauto.
eauto.
Qed.

Lemma RBx_RT_App : forall t t' l l', t ▹▹ t' -> l ▹▹' l' -> (t ·l) ▹▹ (t'· l').
assert (forall t t' l , t ▹▹ t' -> (t ·l) ▹▹ (t'· l)).
induction 1; eauto.
assert (forall t l l' , l ▹▹' l' -> (t ·l) ▹▹ (t· l')).
induction 1; eauto.
eauto.
Qed.

Lemma RBx_RT_CVar  : forall x l1 l2 l1' l2', l1 ▹▹' l1' -> l2 ▹▹'  l2' -> 
  x ## l1 · l2  ▹▹   x ## (l1'@l2').
intros.
eapply RBx_RT_trans2. apply RBx_RT_App. apply RBx_RT_Var. apply H.
apply H0.
apply RBx_RT_onestep. constructor.
Qed.

Lemma RBx_RT_CTerm  : forall t t' l1 l2 l1' l2', l1 ▹▹' l1' -> l2 ▹▹'  l2' -> 
  t ▹▹ t' ->
  t · l1 · l2  ▹▹   t' · (l1'@l2').
intros.
eapply RBx_RT_trans2. apply RBx_RT_App. apply RBx_RT_App. apply H1.
apply H. apply H0.
apply RBx_RT_onestep. constructor.
Qed.

Lemma Rx_RT_List_onestep_trans : forall t t', t →→ t' -> forall l l', l →→' l' -> 
 t ::: l →→' t' ::: l'.
assert (forall t l l', l →→' l' -> 
 t ::: l →→' t ::: l').
induction 1; eauto.
induction 1; intros.
apply H; trivial.
econstructor. constructor. apply H0. intuition.
Qed.
 

Lemma RBx_RT_cons : forall t t' l l' , t ▹▹ t' -> l ▹▹' l' ->
  t ::: l ▹▹' t' ::: l'.
assert (forall t t' l , t ▹▹ t' ->
  t ::: l ▹▹' t' ::: l).
induction 1; eauto. 
assert (forall t  l l', l ▹▹' l' ->
  t ::: l ▹▹' t ::: l').
induction 1; eauto.
eauto.
Qed.


Hint Resolve RBx_RT_La RBx_RT_Pi RBx_RT_App RBx_RT_Var RBx_RT_CVar RBx_RT_CTerm.
Hint Resolve Rx_RT_List_onestep_trans RBx_RT_cons.

Definition proviso t l :=  (exists x, t = (# x)%DN) \/ (exists t1, exists t2, t = (t1·t2)%DN) \/ l <> [[]].

(* Preuve du Lemme 204 *)
Lemma L204_1 : forall t , (xNTerm (DN_to_SC t) /\ (forall l, xNTerm_List l /\ (proviso t l) -> xNTerm (DN_to_SC t) /\ xNTerm (DN_to_SC_List l t))).

induction t; split; simpl; intros; eauto.
destruct H; intuition.
destruct H; intuition.
subst. unfold proviso in H0. destruct H0. destruct H0; discriminate.
destruct H0. destruct H0 as ( ? & ? & ?); discriminate. apply H0; trivial.

destruct IHt1. destruct (H0 (DN_to_SC t2 ::: [[]])). split.
simpl. destruct IHt2; intuition.
unfold proviso. right; right; intro; discriminate.
trivial.

split.

destruct IHt1. destruct (H1 (DN_to_SC t2 ::: [[]])). split.
simpl. destruct IHt2; intuition.
unfold proviso. right; right; intro; discriminate.
trivial.

destruct IHt1. destruct (H1 (DN_to_SC t2 ::: l)). split.
simpl. destruct IHt2; intuition.
unfold proviso. right; right; intro; discriminate.
trivial.

intuition. intuition.
unfold proviso in H5. destruct H5.
destruct H5; discriminate.
destruct H5. destruct H5 as ( ? & ? & ?); discriminate.
subst. apply H5. trivial.

intuition.
intuition.

unfold proviso in H5. destruct H5.
destruct H5; discriminate.
destruct H5. destruct H5 as ( ? & ? & ?); discriminate.
subst. apply H5. trivial.

Qed.

Lemma Rx_to_RBx : forall t t', t → t' -> t ▹ t'
 with Rx_to_RBx_list : forall l l', l →' l' -> l ▹' l'.
induction 1; intros; simpl; constructor; trivial.
intuition. intuition.

induction 1; intros; simpl; constructor; trivial.
intuition.
Qed.

Lemma Rx_to_RBx_trans : forall t t', t →→ t' -> t ▹▹ t'.

induction 1.
constructor. econstructor.  apply Rx_to_RBx.  apply H. trivial.
Qed. 


Lemma Rx_to_RBx_list_trans : forall l l', l →→' l' -> l ▹▹' l'.

induction 1.
constructor. econstructor.  apply Rx_to_RBx_list.  apply H. trivial.
Qed.


Lemma L204_2 : forall t l l', l ▹' l' -> (DN_to_SC_List l t) ▹ (DN_to_SC_List l' t).
induction t; intros; simpl; eauto.
Qed.

Lemma L204_2_trans : forall t l l', l ▹▹' l' -> (DN_to_SC_List l t) ▹▹ (DN_to_SC_List l' t).
induction 1; intros.
constructor.

econstructor. apply L204_2. apply H. trivial.
Qed.

Lemma L204_2_x : forall t l l', l →' l' -> (DN_to_SC_List l t) → (DN_to_SC_List l' t).
induction t; intros; simpl; eauto.
Qed. 

Lemma L204_2_x_trans : forall t l l', l →→' l' -> (DN_to_SC_List l t) →→ (DN_to_SC_List l' t).
induction 1; intros.
constructor.

econstructor. apply L204_2_x. apply H. trivial.
Qed.


Lemma L204_3 : forall t , ((forall l l' ,(DN_to_SC_List l' t)·l →→ (DN_to_SC_List l'@l t)) /\ (forall l,
  (DN_to_SC t) · l →→ (DN_to_SC_List l t))).
induction t; split; intros; simpl; eauto.
destruct IHt1. apply H.
destruct IHt1. apply H.
Qed.



Lemma L204_4 : forall t , (forall u x, (DN_to_SC t)[ x ← (DN_to_SC u)] →→ DN_to_SC (t[x ← u])%DN) /\
 (forall u x l, (DN_to_SC_List l t) [ x ← (DN_to_SC u)]→→ DN_to_SC_List (l [[ x ← (DN_to_SC u)]]) (t [ x ← u])%DN).
induction t; intros; simpl; split; intros.

destruct (lt_eq_lt_dec v x). destruct s.
simpl. constructor. rewrite DN_to_SC_lift. apply Rx_RT_onestep; constructor.
simpl. constructor.


destruct (lt_eq_lt_dec v x). destruct s.
simpl. constructor. eapply Rx_RT_trans2.
destruct (L204_3 (u ↑ x # 0)%DN).
rewrite DN_to_SC_lift in H0. apply H0. constructor.
simpl. constructor. 

constructor.
constructor.

destruct IHt1. destruct IHt2.
eapply Rx_RT_trans2. apply H0. simpl. apply L204_2_x_trans.
apply Rx_RT_List_onestep_trans. apply H1. constructor.

destruct IHt1. destruct IHt2.
eapply Rx_RT_trans2. apply H0. simpl. apply L204_2_x_trans.
apply Rx_RT_List_onestep_trans. apply H1. constructor.

destruct IHt1. destruct IHt2.
eauto.
destruct IHt1. destruct IHt2.
eauto.

destruct IHt1. destruct IHt2.
eauto.
destruct IHt1. destruct IHt2.
eauto.
Qed. 


Lemma L205: (forall M,  xNTerm M ->  M = DN_to_SC (SC_to_DN M)) /\
 (forall l, xNTerm_List l -> forall t, proviso t l -> DN_to_SC_List l t = DN_to_SC (SC_to_DN_List t l)).
apply term_ind; intros; simpl; intuition.
rewrite <- H1. simpl. trivial.
unfold proviso; eauto.
rewrite <- H0. simpl in H1. destruct H1 as (? & ? & ?).
induction t; intuition.
simpl. f_equal. apply H. simpl; intuition.
simpl. f_equal. apply H. simpl; intuition.

simpl in H1; intuition.
unfold proviso. simpl in H1; intuition.
simpl in H1. f_equal; intuition.
simpl in H1. f_equal; intuition.

unfold proviso in H0. destruct H0.
 destruct H0; subst; simpl. trivial.
 destruct H0.  destruct H0 as (t1 & t2 & ?); subst; simpl. trivial.
 elim H0; trivial.

 rewrite <- H0. simpl. rewrite <- H. trivial. 
 simpl in H1; intuition. simpl in H1; intuition.

 unfold proviso. right; left. exists t1; exists (SC_to_DN t); trivial.
Qed.

Definition Betas_norefl t t' := exists u , t ▹ u /\ u ▹▹ t'.

Notation " t ▹▹+ t' " := (Betas_norefl t t') (at level 5) : SC_scope.

(* Bx strongly simulates Beta throught DN_to_SC *)
Lemma L206_1 : forall M M' N, N = DN_to_SC M -> (M → M')%DN -> 
  N ▹▹+ (DN_to_SC M').
 intros.
 generalize dependent N.
assert (((DN_to_SC M ) ▹▹+ (DN_to_SC M')) /\ (forall l, (DN_to_SC_List l M) ▹▹+ (DN_to_SC_List l M'))).
induction H0; unfold Betas_norefl; intros; simpl; split.
  exists ((DN_to_SC b) [← (DN_to_SC c)]· [[]]); split.
  constructor.
  eapply RBx_RT_trans. constructor.
  destruct (L204_4 b) as (? & _).
  apply Rx_to_RBx_trans. apply H.

  intros.  exists ((DN_to_SC b) [← (DN_to_SC c)]· l); split. constructor.
  apply Rx_to_RBx_trans. eapply Rx_RT_trans2.
  apply Rx_RT_App. destruct (L204_4 b) as (? & _). apply H. constructor.
  destruct (L204_3 (b [ ← c])%DN) as (_ & ?). apply H.

  destruct IHBeta.
  destruct (H1 (DN_to_SC z ::: [[]])) as ( ll & ? & ?). eauto.
  intros. destruct IHBeta.  
  destruct (H1 (DN_to_SC z ::: l)) as ( ll & ? & ?). eauto.

  destruct IHBeta. destruct H as (uu & ? & ?).
  exists (DN_to_SC_List (uu ::: [[]]) z); split.
  apply L204_2. constructor. trivial.
  apply L204_2_trans; apply RBx_RT_cons; intuition.
  intros.  destruct IHBeta. destruct H as (uu & ? & ?).
  exists (DN_to_SC_List (uu ::: l) z); split.
  apply L204_2. constructor. trivial.
  apply L204_2_trans; apply RBx_RT_cons; intuition.

  destruct IHBeta. destruct H as (uu & ? & ?).
  exists (λ[DN_to_SC A], uu); intuition.
  intros. destruct IHBeta. destruct H as (uu & ? & ?).
  exists ((λ[DN_to_SC A], uu)·l); intuition.
  destruct IHBeta. destruct H as (uu & ? & ?).
  exists (λ[uu], DN_to_SC x); intuition.
  intros. destruct IHBeta. destruct H as (uu & ? & ?).
  exists ((λ[uu],DN_to_SC x)·l); intuition.

  destruct IHBeta. destruct H as (uu & ? & ?).
  exists (Π(DN_to_SC A), uu); intuition.
  intros. destruct IHBeta. destruct H as (uu & ? & ?).
  exists ((Π(DN_to_SC A), uu)·l); intuition.
  destruct IHBeta. destruct H as (uu & ? & ?).
  exists (Π(uu), DN_to_SC x); intuition.
  intros. destruct IHBeta. destruct H as (uu & ? & ?).
  exists ((Π(uu),DN_to_SC x)·l); intuition.

destruct H. intros.
destruct H as (z & ? & ?).
subst; exists z; intuition.
Qed.

Lemma RBx_trans_strict_flex : forall t t', t ▹▹+ t' -> t ▹▹ t'.
intros.
destruct H as (? & ? & ?).
econstructor. apply H. trivial.
Qed.


Lemma SC_to_DN_lift : forall t n m, SC_to_DN ( t ↑ n # m) =  ((SC_to_DN t) ↑ n # m)%DN
 with SC_to_DN_lift_list : forall l t n m , SC_to_DN_List (t↑n # m)%DN (l ↑↑ n # m) = ((SC_to_DN_List t l)↑n#m)%DN.
induction t; simpl; intros.
rewrite <- SC_to_DN_lift_list. simpl. destruct (le_gt_dec m (n+v)).
destruct (le_gt_dec m v). simpl. trivial.
simpl. trivial.
destruct (le_gt_dec m v). simpl. trivial. simpl. trivial.
trivial.
rewrite IHt. rewrite SC_to_DN_lift_list. trivial. 
rewrite IHt1. rewrite IHt2. trivial.
rewrite IHt1. rewrite IHt2. trivial.

induction l; simpl; intros.
trivial.
rewrite SC_to_DN_lift.
rewrite <- IHl. simpl. trivial.
Qed. 

Lemma SC_to_DN_subst : forall t u x , SC_to_DN (t [ x ← u]) = (((SC_to_DN t) [x ←(SC_to_DN u)])%DN)
 with SC_to_DN_subst_List : forall l t u x, SC_to_DN_List (t[x ← (SC_to_DN u)])%DN (l [[ x ← u]]) = ((SC_to_DN_List t l) [x ←(SC_to_DN u)])%DN.
induction t; simpl; intros.
rewrite <- SC_to_DN_subst_List. simpl.
destruct (lt_eq_lt_dec v x). destruct s. simpl.  trivial.
simpl. rewrite SC_to_DN_lift. trivial. 
simpl. trivial.

trivial.
rewrite IHt. rewrite SC_to_DN_subst_List. trivial.
rewrite IHt1; rewrite IHt2; trivial.
rewrite IHt1; rewrite IHt2; trivial.

induction l; simpl; intros.
trivial.
rewrite <- IHl. rewrite SC_to_DN_subst. simpl. trivial.
Qed.

Lemma SC_to_DN_List_append : forall l l' x, SC_to_DN_List (SC_to_DN_List x l) l' = (SC_to_DN_List x l @ l').
induction l; intros.
 simpl. trivial.
 simpl. rewrite IHl. trivial.
Qed.

Lemma B_aux : forall t t' l, (t →→ t')%DN -> ((SC_to_DN_List t l) →→ (SC_to_DN_List t' l))%DN.
assert (forall l t t', (t→ t')%DN -> ((SC_to_DN_List t l) → (SC_to_DN_List t' l))%DN).
clear.
induction l; simpl; intros; intuition.
induction 1; intros.
constructor. constructor; apply H; trivial.
eauto.
Qed.



Lemma L206_2_aux : forall M N, M ▹ N -> ((SC_to_DN M) →→ (SC_to_DN N))%DN
 with L206_2_aux_list : forall l l', l ▹' l' -> forall y, ((SC_to_DN_List y l) →→ (SC_to_DN_List y l'))%DN.

induction 1; intros; simpl; intuition.
rewrite SC_to_DN_subst. 
apply B_aux. constructor. constructor.

rewrite SC_to_DN_List_append; intuition.
rewrite SC_to_DN_List_append; intuition.

apply B_aux. trivial.

induction 1; intros; simpl; intuition.
apply B_aux. intuition.
Qed.

Lemma L206_2_aux' : forall M N, M → N ->  (SC_to_DN M) = (SC_to_DN N) 
 with L206_2_aux'_list : forall l l', l →' l' -> forall y, (SC_to_DN_List y l) =  (SC_to_DN_List y l').
induction 1; simpl; intros.
trivial.
rewrite SC_to_DN_List_append. trivial.
rewrite SC_to_DN_List_append. trivial.
rewrite IHRx; trivial.
rewrite IHRx; trivial.
rewrite IHRx; trivial.
rewrite (L206_2_aux'_list l l' H (SC_to_DN s)). trivial.
rewrite (L206_2_aux'_list l l' H (#x)%DN). trivial.
rewrite IHRx; trivial. rewrite IHRx; trivial.

induction 1;simpl; intros.
rewrite (L206_2_aux' t t' H). trivial.
rewrite IHRx_list; trivial.
Qed.

Lemma L206_2_aux'_trans : forall M N, M →→ N ->  (SC_to_DN M) = (SC_to_DN N) 
 with L206_2_aux'_list_trans : forall l l', l →→' l' -> forall y, (SC_to_DN_List y l) =  (SC_to_DN_List y l').
induction 1; intros.
trivial.
rewrite <- IHRx_RT. apply L206_2_aux'. trivial.
induction 1; intros.
trivial.
rewrite <- IHRx_RT_List. apply L206_2_aux'_list. trivial.
Qed.


Lemma xNTerm_List_append : forall l l', xNTerm_List l -> xNTerm_List l' ->
     xNTerm_List l@l'.
induction l; intros; simpl in *.
trivial.
destruct H; intuition.
Qed.

Lemma aux_empty_list  : forall l, l →→' [[]] -> l = [[]].
assert (forall l, l →' [[]] -> l = [[]]).
induction l; intuition.
 inversion H.
intros. remember [[]] as L.
induction H0; subst. trivial.
apply H. rewrite IHRx_RT_List in H0. trivial. trivial. trivial.
Qed.

(* I'm sure there is a shorter proof of this statement *)
Lemma Rx_is_normal : forall M , xNTerm M \/ (exists N, (M →→ N /\ xNTerm N))
 with Rx_List_is_normal : forall l, xNTerm_List l \/ (exists l', (l →→' l' /\ xNTerm_List l')).
induction M; simpl.
destruct (Rx_List_is_normal t). left; trivial.
destruct H as (l' & ? &?).  right.
exists (v ## l'); split. apply Rx_RT_Var; trivial. simpl; trivial.
left; trivial.
destruct IHM. destruct (Rx_List_is_normal t).
destruct M; simpl in *. right; exists (v ## (t0@t)); split.
clear. induction t0; simpl; eauto.
simpl.
apply xNTerm_List_append; trivial.
destruct t.
right. exists !s. split; intuition.
left; intuition. discriminate.
right. destruct H as ( ? & ? & ?). exists (M · (t0@t)); split.
clear; induction t0; simpl; eauto.
simpl. intuition. apply xNTerm_List_append; trivial.
replace t0 with [[]] in H2. apply H2; trivial.
destruct t0; simpl in H3; subst; trivial. discriminate.
destruct t.
right. exists (Π (M1), M2); simpl; intuition.
left; intuition. discriminate.
destruct t.
right. exists (λ[M1], M2); simpl; intuition.
left; intuition. discriminate.
destruct H0 as (l' & ? & ?).
destruct M; simpl in *. right. exists (v ## t0 @l'); split.
 apply Rx_RT_CVar. constructor. trivial. simpl.
 apply xNTerm_List_append; trivial.
destruct t. right. exists !s. intuition.
 right. exists ( !s ·  l'); split. apply Rx_RT_App; intuition. simpl; intuition.
rewrite H2 in H0.
apply aux_empty_list in H0. discriminate.
destruct H as ( ? & ? &?).
right. exists (M · t0@l'); split.
apply Rx_RT_CTerm; trivial. simpl; intuition.
apply xNTerm_List_append; trivial.  destruct t0.
apply H3; trivial. simpl in H4; discriminate.
destruct H.
right. destruct t. exists (Π (M1), M2); split.
apply Rx_RT_onestep; constructor. simpl; split; trivial.
exists ((Π (M1), M2) · l'); split.
apply Rx_RT_App. constructor. trivial. simpl; intuition.
subst. apply  aux_empty_list in H0. discriminate.
destruct H.
right. destruct t. exists (λ[M1], M2); split.
apply Rx_RT_onestep; constructor. simpl; split; trivial.
exists ((λ[M1], M2) · l'); split.
apply Rx_RT_App. constructor. trivial. simpl; intuition.
subst. apply  aux_empty_list in H0. discriminate.

right.
(*  cas looooooong *)
assert (  exists l' : Term_List, (t →→' l') /\ xNTerm_List l').
destruct (Rx_List_is_normal t). exists t; intuition.
trivial.
destruct H0 as (l' & ? & ?).
destruct H as (N & ? & ?).
destruct N; simpl in H2.
exists (v ## (t0@l'));split.
eapply Rx_RT_trans2. apply Rx_RT_App. apply H. apply H0.
apply Rx_RT_onestep; constructor. 
simpl. apply xNTerm_List_append; trivial.
destruct l'. apply aux_empty_list in H0; subst.
exists (!s ); split.
eapply Rx_RT_trans2. apply Rx_RT_App. apply H. constructor.
apply Rx_RT_onestep; constructor.  simpl; trivial.
exists (!s  · (t0 ::: l')); split.
apply Rx_RT_App; trivial.
 inversion H1; subst; clear H1.
simpl; intuition. discriminate.
destruct H2 as( ? & ?& ?). destruct N.
elim H2. exists (!s · (t0@l')); split.
eapply Rx_RT_trans2. apply Rx_RT_App. apply H. apply H0.
apply Rx_RT_CTerm; constructor. 
 simpl; intuition. apply xNTerm_List_append; trivial. 
 destruct t0. apply H4; trivial. simpl in H5; discriminate.
elim H2. destruct H2.
  exists ( (Π (N1), N2) · (t0 @ l')); split.
eapply Rx_RT_trans2. apply Rx_RT_App. apply H. apply H0.
apply Rx_RT_CTerm; constructor. 
 simpl; intuition. apply xNTerm_List_append; trivial.
 destruct t0. apply H4; trivial. simpl in H6; discriminate.
destruct H2.
  exists ( (λ  [N1], N2) · (t0 @ l')); split.
eapply Rx_RT_trans2. apply Rx_RT_App. apply H. apply H0.
apply Rx_RT_CTerm; constructor. 
 simpl; intuition. apply xNTerm_List_append; trivial.
 destruct t0. apply H4; trivial. simpl in H6; discriminate.
destruct l'. apply aux_empty_list in H0; subst.
  exists ( (Π (N1), N2) ); split.
  eapply Rx_RT_trans2. apply Rx_RT_App. apply H. constructor.
 apply Rx_RT_onestep. constructor. simpl; trivial.
  exists ( (Π (N1), N2) · (t0:::l')); split.
apply Rx_RT_App; intuition.
inversion H1; subst; clear H1.
 simpl; intuition. discriminate.
destruct l'. apply aux_empty_list in H0; subst.
  exists ( (λ[N1], N2) ); split.
  eapply Rx_RT_trans2. apply Rx_RT_App. apply H. constructor.
 apply Rx_RT_onestep. constructor. simpl; trivial.
  exists ( (λ[N1], N2) · (t0::: l')); split.
apply Rx_RT_App; intuition.
inversion H1; subst; clear H1.
 simpl; intuition. discriminate.
(* pfiou *)
 destruct IHM1; destruct IHM2.
left; split; trivial.
destruct H0 as (N & ? & ?).
right.
exists (Π(M1),N); split.
apply Rx_RT_Pi; intuition. simpl; intuition.
destruct H as (N & ? & ?).
right.
exists (Π(N),M2); split.
apply Rx_RT_Pi; intuition. simpl; intuition.
 destruct H as (N1 & ? & ?); destruct H0 as (N2 & ? & ?).
right.
exists (Π(N1),N2); split.
apply Rx_RT_Pi; intuition. simpl; intuition.

 destruct IHM1; destruct IHM2.
left; split; trivial.
destruct H0 as (N & ? & ?).
right.
exists (λ[M1],N); split.
apply Rx_RT_La; intuition. simpl; intuition.
destruct H as (N & ? & ?).
right.
exists (λ[N],M2); split.
apply Rx_RT_La; intuition. simpl; intuition.
 destruct H as (N1 & ? & ?); destruct H0 as (N2 & ? & ?).
right.
exists (λ[N1],N2); split.
apply Rx_RT_La; intuition. simpl; intuition.

(** list **)
induction l; simpl.
left; trivial.
destruct IHl.
destruct (Rx_is_normal t).
left; split; trivial.
destruct H0 as (t' & ? & ?).
right. exists (t' ::: l); intuition.
simpl; split; trivial.
destruct H as (l' & ? & ?).
right.
destruct (Rx_is_normal t).
exists (t ::: l'); split.
apply Rx_RT_cons. constructor. trivial. simpl; split; trivial.
destruct H1 as (t'& ?& ?).
exists (t' ::: l'); split.
apply Rx_RT_cons. trivial. trivial. simpl; split; trivial.
Qed.



Lemma L206_2 : (forall M M' N, N = DN_to_SC M -> (M → M')%DN -> N ▹▹ (DN_to_SC M')) /\
               (forall M M' N, N = SC_to_DN M -> M ▹ M' -> (N →→ (SC_to_DN M'))%DN) /\
               (forall M , M →→ DN_to_SC (SC_to_DN M)) /\
               (forall N, SC_to_DN (DN_to_SC N) = N /\ forall l, SC_to_DN (DN_to_SC_List l N) = SC_to_DN_List N l).
split; intros.
apply RBx_trans_strict_flex. eapply L206_1. apply H. trivial.

split; intros.
subst. apply L206_2_aux; trivial.

split; intros.
destruct (Rx_is_normal M).
destruct L205 as ( ? & _). pattern M at 1. rewrite (H0 M H). constructor.
destruct H as (N & ? & ?). 
apply Rx_RT_trans2 with N; trivial.
apply L206_2_aux'_trans in H. rewrite H.
destruct L205 as ( ? & _). pattern N at 1. rewrite (H1 N H0). constructor.

induction N; simpl; split; intros; trivial.
destruct IHN1; destruct IHN2.
rewrite H0. simpl. rewrite H1. trivial.
destruct IHN1; destruct IHN2.
rewrite H0. simpl. rewrite H1. trivial.
destruct IHN1; destruct IHN2.
rewrite H. rewrite H1. trivial. 
destruct IHN1; destruct IHN2.
rewrite H. rewrite H1. trivial.
destruct IHN1; destruct IHN2.
rewrite H. rewrite H1. trivial.
destruct IHN1; destruct IHN2.
rewrite H. rewrite H1. trivial.
Qed.


Lemma RBx_diamond  : forall M M1 M2, M ▹▹ M1 -> M ▹▹ M2 -> 
  exists M', M1 ▹▹ M' /\ M2 ▹▹ M'.
intros.

assert (forall M M' N, N = SC_to_DN M -> M ▹▹ M' -> ( N →→ (SC_to_DN M')))%DN.
clear.
intros; subst. induction H0; intuition.
apply dn_red.Betas_trans with (SC_to_DN t); trivial.
destruct L206_2 as ( _ & ? & _). eapply H1.
reflexivity. trivial.

(* 
   reflection on the SC world into DN world 
   and use the fact that DN world is confluent
*)
destruct (dn_red.Betas_diamond (SC_to_DN M) (SC_to_DN M1) (SC_to_DN M2)); eauto.
destruct H2.
(* we have a candidate in DN *)

clear H1.
assert (forall M M' N, N = DN_to_SC M -> (M →→ M')%DN -> N ▹▹ (DN_to_SC M')) .
clear.
intros. subst. induction H0.
constructor. destruct L206_2 as ( ? & _). eapply H0.
reflexivity. trivial.
eauto.

(* so we go back to SC *)
assert (DN_to_SC (SC_to_DN M1) ▹▹ DN_to_SC x).
eapply H1. reflexivity. trivial.
assert (DN_to_SC (SC_to_DN M2) ▹▹ DN_to_SC x).
eapply H1. reflexivity. trivial.

destruct L206_2 as ( _ & _ & ?& _).

(* and prove that the translation of our candidate is valid *)
exists (DN_to_SC x); split.
eapply RBx_RT_trans2. apply Rx_to_RBx_trans. apply H6. trivial.
eapply RBx_RT_trans2. apply Rx_to_RBx_trans. apply H6. trivial.

Qed.

Reserved Notation "A ≡ B "  (at level 80, no associativity).
Reserved Notation "A ≡' B "  (at level 80, no associativity).

Inductive RBx_RST : Term -> Term -> Prop :=
 | RBx_RST_intro : forall s t, s ▹▹ t -> s ≡ t
 | RBx_RST_sym : forall s t, t ≡ s -> s ≡ t
 | RBx_RST_trans : forall s t u, s ≡ t -> t ≡ u -> s ≡ u
where "s ≡ t " := (RBx_RST s t) : SC_scope
with RBx_RST_list : Term_List -> Term_List -> Prop :=
 | RBx_RST_intro' : forall l l', l ▹▹' l' -> l ≡' l'
 | RBx_RST_sym' : forall l l', l' ≡' l -> l ≡' l'
 | RBx_RST_trans' : forall  j k l, j ≡' k -> k ≡' l -> j ≡' l
where "j ≡' k" := (RBx_RST_list j k) : SC_scope.

Hint Constructors RBx_RST RBx_RST_list.

Lemma RBx_RST_confl : forall s t , s ≡ t -> exists z, (s ▹▹ z /\ t ▹▹ z).
(* with RBx_RST_list_confl : forall l l' , l ≡' l' -> exists z, (l ▹▹' z /\ l' ▹▹' z).*)
induction 1.
exists t; split; trivial; constructor.
destruct IHRBx_RST as (z & ? & ?); exists z; split; trivial.
destruct IHRBx_RST1 as (z1 & ? & ?); destruct IHRBx_RST2 as (z2 & ? &?).
destruct (RBx_diamond t z1 z2 H2 H3) as (z3 & ? & ?).
exists z3; eauto.
Qed.



Lemma RBx_RT_sort : forall s t, !s  ▹▹ t  -> t = !s.
intros.
remember !s as S.
induction H; subst; try discriminate.
trivial.
inversion H.
Qed.

Lemma RBx_RST_sort : forall s t , !s ≡ t -> t ▹▹ !s.
intros.
apply RBx_RST_confl in H as (z & ? & ?).
apply RBx_RT_sort in H. subst. trivial.
Qed.

Lemma RBx_RST_sort2 : forall s t, !s ≡ !t -> s = t.
intros.
apply RBx_RST_sort in H. apply RBx_RT_sort in H. injection H; intuition.
Qed.

Lemma RBx_RT_to_Pi :forall A B T, Π(A),B ▹▹ T ->  exists C, exists D, 
  T = Π(C),D /\ A ▹▹ C /\ B ▹▹ D.
intros. remember (Π(A),B) as P. 
generalize dependent A. generalize dependent B.
induction H;intros;  subst; try discriminate.
exists A; exists B; intuition.
inversion H; subst; clear H.
destruct (IHRBx_RT D A) as (A1 & B1 & ? & ? & ?); trivial.
exists A1; exists B1; eauto.
destruct (IHRBx_RT B C) as (A1 & B1 & ? & ? & ?); trivial.
exists A1; exists B1; eauto.
Qed.

Lemma RBx_RST_to_Pi : forall A B C D, Π(A),B ≡ Π(C),D  -> A ≡ C /\ B ≡ D.
intros.
apply RBx_RST_confl in H. destruct H as (z & ? & ?).
apply RBx_RT_to_Pi in H; apply RBx_RT_to_Pi in H0.
destruct H as (A' & B' & ? & ? & ?).
destruct H0 as (A'' & B'' & ? & ? & ?).
rewrite H in H0; injection H0; intros; subst; clear H0.
split. eapply RBx_RST_trans. constructor. apply H1. eauto.
eapply RBx_RST_trans. constructor. apply H2. eauto.
Qed.

Lemma RBx_RST_sort_pi : forall A B s,~(Π(A),B ≡ !s).
intros; intro.
apply RBx_RST_sym in H. apply RBx_RST_sort in H. apply RBx_RT_to_Pi in H.
destruct H as (? & ? & ? & _ & _); discriminate.
Qed.


Lemma RBx_lift : forall s t , s ▹ t -> forall n m, s ↑ n # m ▹  t ↑ n # m 
 with RBx_list_lift : forall j k , j ▹' k -> forall n m, j ↑↑ n # m ▹' k ↑↑ n # m.
destruct 1; simpl; intros.
destruct substP1 as ( ? & _).
change m with (0+m); rewrite H; trivial.
constructor.
destruct (le_gt_dec m x). rewrite append_lift. constructor.
rewrite append_lift. constructor.
rewrite append_lift. constructor.
constructor; apply RBx_lift; trivial.
constructor; apply RBx_lift; trivial.
constructor; apply RBx_lift; trivial.
constructor. apply RBx_list_lift; trivial.
destruct (le_gt_dec m x). constructor. apply RBx_list_lift; trivial.
constructor. apply RBx_list_lift; trivial.
constructor; apply RBx_lift; trivial.
constructor; apply RBx_lift; trivial.
(** list **)
destruct 1; simpl; intros.
constructor. apply RBx_lift; trivial.
constructor. apply RBx_list_lift; trivial.
Qed.

Lemma RBx_RT_lift : forall s t , s ▹▹ t -> forall n m, s ↑ n # m ▹▹  t ↑ n # m .
induction 1; intros; eauto.
eapply RBx_RT_trans. apply RBx_lift. apply H. intuition. 
Qed.

Lemma RBx_RT_List_lift : forall j k , j ▹▹' k -> forall n m, j ↑↑ n # m ▹▹' k ↑↑ n # m.
induction 1; intros; eauto.
eapply RBx_RT_List_trans. apply RBx_list_lift. apply H. intuition.
Qed.

Lemma RBx_RST_lift : forall s t , s ≡ t -> forall n m, s ↑ n # m ≡ t ↑ n # m .
induction 1; intros; eauto.
constructor. eapply RBx_RT_lift; intuition. 
Qed.

Lemma RBx_RST_List_lift : forall s t , s ≡' t -> forall n m, s ↑↑ n # m ≡' t ↑↑ n # m .
induction 1; intros; eauto.
constructor. eapply RBx_RT_List_lift; intuition. 
Qed.

Hint Resolve RBx_lift RBx_list_lift RBx_RT_lift RBx_RT_List_lift RBx_RST_lift RBx_RST_List_lift.


Lemma RBx_subst : forall a b ,  a ▹ b -> forall n c,  a[n←c] ▹ b[n←c] 
 with RBx_List_subst:  forall a b ,  a ▹' b ->forall n c,   a[[n←c]] ▹' b[[n←c]] .
destruct 1;simpl;  intros.
destruct subst_travers as ( ? & _). rewrite H.
replace (n+1) with (S n) by omega.
constructor.
constructor.
destruct (lt_eq_lt_dec x n). destruct s. rewrite append_subst;constructor.
rewrite append_subst;constructor.
rewrite append_subst;constructor.
rewrite append_subst;constructor.
constructor. apply RBx_subst. trivial.
constructor. apply RBx_subst. trivial.
constructor. apply RBx_subst. trivial.
constructor. apply RBx_List_subst. trivial.
destruct (lt_eq_lt_dec x n). destruct s. constructor. apply RBx_List_subst; trivial.
constructor. apply RBx_List_subst; trivial.
constructor. apply RBx_List_subst; trivial.
constructor. apply RBx_subst. trivial. constructor. apply RBx_subst. trivial.
(** list **)
destruct 1; simpl; intros.
constructor. apply RBx_subst. trivial. constructor. apply RBx_List_subst. trivial.
Qed.

Lemma RBx_RT_subst : forall a b ,  a ▹▹ b -> forall n c,  a[n←c] ▹▹ b[n←c] .
induction 1; simpl; intros; eauto.
econstructor. eapply RBx_subst. apply H. auto. 
Qed.

Lemma RBx_RT_List_subst:  forall a b ,  a ▹▹' b ->forall n c,   a[[n←c]] ▹▹' b[[n←c]] .
induction 1; simpl; intros; eauto.
econstructor. eapply RBx_List_subst.  apply H. auto.
Qed.

Lemma RBx_RST_subst : forall a b ,  a ≡ b -> forall n c,  a[n←c] ≡ b[n←c] .
induction 1; simpl; intros; eauto.
constructor. apply RBx_RT_subst. trivial.
Qed.

Lemma RBx_RST_List_subst : forall a b ,  a ≡' b -> forall n c,  a[[n←c]] ≡' b[[n←c]] .
induction 1; simpl; intros; eauto.
constructor. apply RBx_RT_List_subst. trivial.
Qed.

Hint Resolve RBx_subst RBx_List_subst RBx_RT_subst RBx_RT_List_subst RBx_RST_subst RBx_RST_List_subst.

Lemma RBx_RST_La : forall A B s t, A ≡ B -> s ≡ t -> λ[A],s ≡ λ[B],t.
assert (forall A B s , A ≡ B -> λ[A],s ≡ λ[B],s).
induction 1; eauto.
assert (forall A s t, s ≡ t -> λ[A],s ≡ λ[A],t).
induction 1; eauto.
eauto.
Qed.

Lemma RBx_RST_Pi : forall A B C D, A ≡ B -> C ≡ D-> Π(A),C ≡ Π(B),D.
assert (forall A B C , A ≡ B -> Π(A),C ≡ Π(B),C).
induction 1; eauto.
assert (forall A C D, C ≡ D -> Π(A),C ≡ Π(A),D).
induction 1; eauto.
eauto.
Qed.

Lemma RBx_RST_App : forall t t' l l', t ≡ t' -> l ≡' l' -> (t ·l) ≡ (t'· l').
assert (forall t t' l , t ≡ t' -> (t ·l) ≡ (t'· l)).
induction 1; eauto.
assert (forall t l l' , l ≡' l' -> (t ·l) ≡ (t· l')).
induction 1; eauto.
eauto.
Qed.

Hint Resolve RBx_RST_La RBx_RST_Pi RBx_RST_App.

Lemma RBx_RST_Var : forall x l l', l ≡' l' -> x ## l ≡ x ## l'.
induction 1; eauto.
Qed.

Lemma RBx_RST_CVar  : forall x l1 l2 l1' l2', l1 ≡' l1' -> l2 ≡'  l2' -> 
  x ## l1 · l2  ≡   x ## (l1'@l2').
intros.
eapply RBx_RST_trans.  apply RBx_RST_App. apply RBx_RST_Var. apply H.
apply H0.
constructor. apply RBx_RT_onestep. constructor.
Qed.

Lemma RBx_RST_CTerm  : forall t t' l1 l2 l1' l2', l1 ≡' l1' -> l2 ≡'  l2' -> 
  t ≡ t' ->
  t · l1 · l2  ≡   t' · (l1'@l2').
intros.
eapply RBx_RST_trans. apply RBx_RST_App. apply RBx_RST_App. apply H1.
apply H. apply H0.
constructor; apply RBx_RT_onestep. constructor.
Qed.

Lemma RBx_RST_cons : forall t t' l l' , t ≡ t' -> l ≡' l' ->
  t ::: l ≡' t' ::: l'.
assert (forall t t' l , t ≡  t' ->  t ::: l ≡' t' ::: l).
induction 1; eauto.
assert (forall t  l l', l ≡' l' ->   t ::: l ≡' t ::: l').
induction 1; eauto.
eauto.
Qed.

Hint Resolve RBx_RST_Var RBx_RST_CVar RBx_RST_CTerm RBx_RST_cons.

Lemma RBx_RST_subst2 : forall a s t ,  s ≡ t ->forall n,  a[n←s] ≡ a[n←t] 
 with RBx_RST_List_subst2 : forall l s t , s ≡ t ->forall n,  l[[n←s]] ≡' l[[n←t]] .
destruct a; intros; simpl; intuition.
destruct (lt_eq_lt_dec v n); intuition.

destruct l; intros; simpl; intuition.
Qed.

