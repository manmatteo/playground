Require Import sc_term. 
Require Import sc_red.
Require Import sc_context. 
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.
Require Import List.

Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ; A ⊢ l : T" (at level 80, A, l, T at level 30, no associativity) .
Reserved Notation "Γ ⊣ " (at level 80, no associativity).

Parameter Ax : Sorts -> Sorts -> Prop.
Parameter Rel : Sorts -> Sorts -> Sorts -> Prop.

Inductive wf : Env -> Prop :=
 | wf_nil : nil ⊣
 | wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : SC_scope
with typ : Env -> Term -> Term -> Prop :=
 | typ_sort : forall Γ s1 s2, Ax s1 s2 -> Γ ⊣  -> Γ ⊢ !s1 : !s2
 | typ_pi : forall Γ s1 s2 s3 A B, Rel s1 s2 s3 ->
    Γ ⊢ A : !s1 -> A::Γ ⊢ B : !s2 -> Γ ⊢ Π(A),B : !s3
 | typ_la : forall Γ A B M s, Γ ⊢ Π(A),B : !s -> A::Γ ⊢ M : B ->
    Γ ⊢ λ[A],M : Π(A),B
 | typ_var : forall Γ v A B l, Γ;A ⊢ l : B ->  A ↓ v  ⊂ Γ -> 
   Γ ⊢ v ## l : B
 | typ_app (*cut3*): forall Γ M A B l, Γ ⊢ M : A -> Γ ; A ⊢ l : B ->
    Γ ⊢ M · l : B
 | typ_conv : forall Γ M A B s, Γ ⊢ M : A -> Γ ⊢ B : !s -> A ≡ B ->
  Γ ⊢ M : B
where "Γ ⊢ t : T" := (typ Γ t T) : SC_scope
with typ_list : Env -> Term -> Term_List -> Term -> Prop :=
 | typ_list_ax : forall Γ A s, Γ ⊢ A :!s -> Γ ; A ⊢ [[]] : A
 | typ_list_pi : forall Γ A B s M l C, Γ ⊢ Π(A),B : !s -> Γ ⊢ M : A -> 
   Γ ;B[ ← M]  ⊢ l : C -> Γ ; Π(A),B ⊢ M ::: l : C
 | typ_list_conv_r : forall Γ C l A B s, Γ ; C ⊢ l :A -> Γ ⊢ B : !s -> A ≡ B ->
  Γ ; C ⊢ l : B
 | typ_list_conv_l : forall Γ A l C B s , Γ ; A ⊢ l : C -> Γ ⊢ B : !s -> A ≡ B ->
    Γ; B ⊢ l : C
where "Γ ; A ⊢ l : T" := (typ_list Γ A l T) : SC_scope.

Hint Constructors wf typ typ_list.

Scheme typ_ind' := Induction for typ Sort Prop
      with typ_list_ind' := Induction for typ_list Sort Prop
      with wf_ind' := Induction for wf Sort Prop.

Combined Scheme typ_induc from typ_ind', typ_list_ind', wf_ind'.


Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣ /\ (exists s, T = !s \/ Γ ⊢ T : !s)
 with wf_typ_list :  forall Γ A t T, Γ; A ⊢ t : T -> Γ ⊣ /\ (exists s, T = !s \/ Γ ⊢ T : !s).
destruct 1; split; trivial.
exists s2; left; trivial.
eapply wf_typ. apply H0.
exists s3; left; trivial.
eapply wf_typ. apply H.
exists s; right; trivial.
eapply wf_typ_list. apply H.
eapply wf_typ_list. apply H.
eapply wf_typ. apply H.
eapply wf_typ_list. apply H0.
eapply wf_typ. apply H.
exists s; right; trivial.
(** list **)
destruct 1; split; trivial.
eapply wf_typ. apply H.
exists s; right; trivial.
eapply wf_typ. apply H0.
eapply wf_typ_list. apply H1.
eapply wf_typ. apply H0.
exists s; right; trivial.
eapply wf_typ. apply H0.
eapply wf_typ_list. apply H.
Qed.

Lemma wf_inv : forall Γ A, A::Γ ⊣ -> Γ ⊣ /\ exists s, Γ ⊢ A : !s .
intros. remember (A::Γ) as L. induction H; subst; try discriminate.
injection HeqL; intros; subst; clear HeqL.
split.
eapply wf_typ. apply H. exists s; trivial.
Qed.

Hint Resolve wf_typ wf_inv.

Definition wf_weak := forall Γ, Γ ⊣ -> forall Δ Γ' n A, ins_in_env Δ A n Γ Γ' -> forall s, Δ ⊢ A : !s -> Γ' ⊣.
Definition typ_weak := forall Δ t T, Δ ⊢ t : T -> forall d Γ  n Δ' s,  ins_in_env Γ d n Δ Δ' ->
                 Γ ⊢ d :!s -> Δ' ⊢ t ↑ 1 # n : T ↑ 1 # n.
Definition typ_list_weak := forall Δ A l T, Δ ; A ⊢ l : T -> forall d Γ  n Δ' s,  ins_in_env Γ d n Δ Δ' ->
                 Γ ⊢ d :!s -> Δ' ; A  ↑ 1 # n ⊢ l ↑↑ 1 # n : T ↑ 1 # n.

Lemma weakening : typ_weak /\ typ_list_weak /\ wf_weak.
apply typ_induc;simpl; intros.
(* typ *)
constructor; eauto. 
(**)
apply typ_pi with s1 s2; trivial.
 change !s1 with (!s1  ↑ 1 # n); eauto. 
 change !s2 with (!s2  ↑ 1 # (S n)).  eapply H0. constructor; apply H1. apply H2.
(**)
apply typ_la with s.
 change !s with (!s  ↑ 1 # n);  eauto.
 eapply H0. constructor;  apply H1.  apply H2.
(**)
destruct (le_gt_dec n v). apply typ_var with A↑ 1 # n. eauto. 
 destruct i as (z & ? & ?). exists z; split.
 rewrite H2; apply liftP3; intuition. eapply ins_item_ge. apply H0. trivial. trivial.
 apply typ_var with A↑ 1 # n. eauto.  eapply ins_item_lift_lt. apply H0. trivial. trivial.
(**)
apply typ_app with A ↑ 1 # n; eauto. 
(**)
apply typ_conv with ( A ↑ 1 # n) s; eauto.
(** list **)
apply typ_list_ax with s. change !s with  ( !s ↑ 1 # n). eauto. 
(**)
apply typ_list_pi with s. change !s with  ( !s ↑ 1 # n). eauto.
 eauto. destruct substP1 as (? & _). change n with (0+n). rewrite <- H4. simpl. eauto.
(**)
apply typ_list_conv_r with (A ↑ 1 # n) s; intuition. eauto. 
change !s with  ( !s ↑ 1 # n). eauto. 
(**)
apply typ_list_conv_l with (A ↑ 1 # n) s; intuition. eauto.
change !s with  ( !s ↑ 1 # n). eauto. 
(* wf *)
inversion H; subst; clear H. apply wf_cons with s; trivial.
(**)
inversion H0; subst; clear H0.
eauto.
apply wf_cons with s. eapply H. apply H6. apply H1.
Qed.

(* same judgment but last rule is not conv rule *)
Reserved Notation "Γ ⊢' t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ; A ⊢' l : T" (at level 80, A, l, T at level 30, no associativity) .

Inductive typ' : Env -> Term -> Term -> Prop :=
 | typ'_sort : forall Γ s1 s2, Ax s1 s2 -> Γ ⊣  -> Γ ⊢' !s1 : !s2
 | typ'_pi : forall Γ s1 s2 s3 A B, Rel s1 s2 s3 ->
    Γ ⊢ A : !s1 -> A::Γ ⊢ B : !s2 -> Γ ⊢' Π(A),B : !s3
 | typ'_la : forall Γ A B M s, Γ ⊢ Π(A),B : !s -> A::Γ ⊢ M : B ->
    Γ ⊢' λ[A],M : Π(A),B
 | typ'_var : forall Γ v A B l, Γ;A ⊢ l : B ->  A ↓ v  ⊂ Γ -> 
   Γ ⊢' v ## l : B
 | typ'_app (*cut3*): forall Γ M A B l, Γ ⊢ M : A -> Γ ; A ⊢ l : B ->
    Γ ⊢' M · l : B
where "Γ ⊢' t : T" := (typ' Γ t T) : SC_scope.


Inductive typ'_list : Env -> Term -> Term_List -> Term -> Prop :=
 | typ'_list_ax : forall Γ A s, Γ ⊢ A :!s -> Γ ; A ⊢' [[]] : A
 | typ'_list_pi : forall Γ A B s M l C, Γ ⊢ Π(A),B : !s -> Γ ⊢ M : A -> 
   Γ ;B[ ← M]  ⊢ l : C -> Γ ; Π(A),B ⊢' M ::: l : C
where "Γ ; A ⊢' l : T" := (typ'_list Γ A l T).

Lemma typ'_typ : forall Γ t T, Γ ⊢' t : T -> Γ ⊢ t : T.
induction 1; intros; simpl in *; eauto.
Qed.

Lemma typ'_list_typ_list : forall Γ C l A, Γ ; C ⊢' l : A -> Γ; C ⊢ l : A.
induction 1; intros; simpl in *; eauto.
Qed.

Hint Constructors typ' typ'_list.
Hint Resolve typ'_typ typ'_list_typ_list.

Lemma StoupCorrect : forall Γ A l T, Γ ; A ⊢ l : T -> exists s, Γ ⊢ A : !s.
induction 1.
exists s; trivial.
exists s; trivial.
trivial.
exists s; trivial.
Qed.

Lemma Gen2a: forall Γ C A , Γ; C ⊢ [[]] : A -> A ≡ C.
intros.
remember [[]] as L; induction H; subst; try discriminate; eauto.
Qed.



Lemma Gen2b: forall Γ C D M l , Γ; D ⊢ M :::l : C -> exists A, exists B, 
  D ≡ Π(A),B /\ Γ; Π(A),B ⊢' M :::l : C /\ Γ ⊢ M : A /\ Γ ;B[ ← M]  ⊢ l : C  .
intros.
remember (M:::l) as L; induction H; subst; try discriminate.
injection HeqL; intros; subst; clear HeqL. 
 clear IHtyp_list. exists A; exists B; intuition; eauto.

 destruct (IHtyp_list (refl_equal (M:::l))) as (A' & B' & ?  & ? & ? & ?); clear IHtyp_list.
 exists A'; exists B'; intuition; eauto.
 assert (exists sp, Γ ⊢ Π (A'), B' : !sp).
    apply typ'_list_typ_list in H3. apply StoupCorrect in H3. trivial. destruct H6 as (sp & ?).
 econstructor.   apply H6. trivial. eauto.

 destruct (IHtyp_list (refl_equal (M:::l))) as (A' & B' & ?  & ? & ? & ?); clear IHtyp_list.
 exists A'; exists B'; intuition; eauto.
Qed.

(* seems useless since we inlined @ and subst *)
Lemma Gen2c: forall Γ C D l , Γ; D ⊢ l : C -> (l <> [[]]) -> (forall M l', l <> M:::l') -> 
  Γ; D ⊢' l : C .
induction 1; intros.
 elim H0; trivial.
 elim (H3 M l); trivial.
 destruct l. elim H2; trivial. elim (H3 t l); trivial.
 destruct l. elim H2; trivial. elim (H3 t l); trivial.
Qed.


Theorem thinning :
   forall Γ t T A s,
      Γ ⊢ A : !s ->
      Γ ⊢ t : T ->
   A::Γ ⊢ t ↑ 1 : T ↑ 1.
intros.
destruct weakening as (? & _).
eapply H1.
apply H0. apply ins_O. apply H.
Qed.

Theorem thinning_n : forall n Δ Δ',   Δ ⊣ -> trunc n Δ Δ' ->
   forall t T , Δ' ⊢ t : T  ->  Δ ⊢ t ↑ n : T ↑ n.
induction n; intros.
inversion H0; subst; clear H0.
destruct lift0 as ( ? & _). rewrite 2! H0; trivial.
inversion H0; subst; clear H0.
change (S n) with (1+n).
replace (t ↑ (1+n)) with ((t ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H; subst; clear H.
eapply thinning ; trivial. apply H2.
eapply IHn. eapply wf_typ. apply H2. apply H3. trivial.
Qed.

Lemma TypeCorrect : forall Γ t T , Γ ⊢ t : T -> exists s, (T = !s \/ Γ ⊢ T : !s)
 with TypeCorrect_list : forall Γ A l T, Γ ; A ⊢ l : T -> exists s, Γ ⊢ T : !s.
destruct 1.
(**)
exists s2;left;  trivial.
(**)
exists s3; left; trivial.
(**)
exists s; right; trivial.
(**)
apply TypeCorrect_list in H. destruct H. exists x; right; trivial.
(**)
apply TypeCorrect_list in H0. destruct H0. exists x; right; trivial.
(**)
exists s; right; trivial.
(** list **)
destruct 1.
(**)
exists s; trivial.
(**)
eapply TypeCorrect_list. apply H1.
(**)
exists s; trivial.
(**)
eapply TypeCorrect_list. apply H.
Qed.



Lemma cut1 :forall l' Γ  C A , Γ ; C ⊢ l' : A -> forall l B, Γ ;A ⊢l : B -> Γ ; C ⊢ l'@l : B.
induction l'; simpl;intros.
destruct (StoupCorrect Γ C [[]] A H) as (sc & ? ).
apply Gen2a in H. apply typ_list_conv_l with A sc; trivial.
destruct (StoupCorrect Γ C (t:::l') A H).
apply Gen2b in H . destruct H  as (A' & B' & ? & ? & ? & ?).
apply typ_list_conv_l with (Π (A'), B') x; trivial.
apply typ'_list_typ_list in H2.
destruct (StoupCorrect Γ (Π (A'), B') (t:::l') A H2).
apply typ_list_pi with x0; trivial. apply IHl' with A; trivial.
apply RBx_RST_sym; trivial.
Qed.

Definition ccut4 := forall Γ t T , Γ  ⊢ t  : T  -> forall Δ P A, Δ  ⊢ P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ' ⊢ t [ n ←P ]  : T [ n ←P ].
Definition ccut2 := forall Γ B l C, Γ ; B  ⊢ l  : C  -> forall Δ P A, Δ  ⊢ P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ'; B[ n ←P]  ⊢ l [[ n ←P ]]  : C [ n ←P ].
Definition ccut_wf := forall Γ ,  Γ ⊣ -> forall Δ P A n Γ' , Δ ⊢ P : A -> 
  sub_in_env  Δ P A n Γ Γ' ->     Γ' ⊣ .

Lemma sub_trunc : forall Γ0 a A n Γ Δ, sub_in_env Γ0 a A n Γ Δ -> trunc n Δ Γ0.
induction 1.
apply trunc_O.
apply trunc_S. trivial.
Qed.


Lemma substitution : ccut4 /\ ccut2 /\ ccut_wf.
apply typ_induc; simpl; intros.
(* typ *)
apply typ_sort. trivial. eauto.
(**)
apply typ_pi with s1 s2; eauto.
(**)
apply typ_la with s; eauto. eapply H0. apply H1. intuition. eapply wf_typ. apply t0.
(**)
destruct (lt_eq_lt_dec v n). destruct s. 
apply typ_var with A[n ← P]. eauto. eapply nth_sub_item_inf. apply H1. intuition. trivial.
apply typ_app with A[n ← P].  destruct i as (z & ?& ?).
subst. destruct substP3 as (? &_ ). rewrite H3; intuition.
rewrite <- (nth_sub_eq H1 H4).
eapply thinning_n.
eapply wf_typ_list.  eapply H. apply H0. apply H1. trivial.
eapply sub_trunc. apply H1. trivial. 
eauto.
apply typ_var with A[n ← P]. eauto.
destruct i as ( z & ? &?). rewrite H3. destruct substP3 as (  ? & _). rewrite H5; intuition.
exists z; intuition.
rewrite <- pred_of_minus.
rewrite <- (S_pred v n l0). reflexivity.
eapply nth_sub_sup. apply H1. intuition.
rewrite <- pred_of_minus.
rewrite <- (S_pred v n l0). trivial.
(**)
apply typ_app with A[n ← P]. eauto. eauto.
(**)
apply typ_conv with A[n ← P] s; eauto. 
(* list *)
apply typ_list_ax with s. eauto.
(**)
apply typ_list_pi with s; eauto. destruct (subst_travers) as ( ? & _).
replace (S n) with (n+1) by intuition.
rewrite <- H5. eauto.
(**)
eapply typ_list_conv_r; eauto. 
(**)
eapply typ_list_conv_l; eauto.
(* wf *)
inversion H0.
(**)
inversion H1; subst; clear H1. 
eapply wf_typ. apply H0.
apply wf_cons with s. eapply H. apply H0. trivial. eapply wf_typ. apply t.
Qed.

Lemma cut4 : forall Γ t T , Γ  ⊢ t  : T  -> forall Δ P A, Δ  ⊢ P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ' ⊢ t [ n ←P ]  : T [ n ←P ].
destruct substitution as (H & _); exact H.
Qed.

Lemma cut2 : forall Γ B l C, Γ ; B  ⊢ l  : C  -> forall Δ P A, Δ  ⊢ P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ'; B[ n ←P]  ⊢ l [[ n ←P ]]  : C [ n ←P ].
destruct substitution as ( _ & H & _); exact H.
Qed.

Lemma cut_wf : forall Γ ,  Γ ⊣ -> forall Δ P A n Γ' , Δ ⊢ P : A -> 
  sub_in_env  Δ P A n Γ Γ' ->     Γ' ⊣ .
destruct substitution as ( _ & _ & ?); exact H.
Qed.

(* reprendre en definition |-* où le dernier pas n'est pas une conversion *)
Lemma Gen1a : forall  Γ s T,  Γ ⊢ !s : T -> exists t,  Γ ⊢' !s : !t /\ T ≡ !t.
intros.
remember !s as S; induction H; subst; try discriminate.
injection HeqS; intros; subst; clear HeqS. exists s2; intuition.
destruct IHtyp1; intuition.
exists x; eauto.
Qed.

Lemma Gen1b: forall  Γ A B T, Γ ⊢ Π ( A ), B : T -> exists s1, exists s2, exists s3, Rel s1 s2 s3 /\
 Γ ⊢' Π ( A ), B : !s3 /\ Γ ⊢ A : !s1 /\ A::Γ ⊢ B : !s2 /\ T ≡ !s3.
intros.
remember ( Π ( A ), B) as P; induction H; subst; try discriminate.
injection HeqP; intros; subst; clear HeqP IHtyp1 IHtyp2.
exists s1; exists s2; exists s3; intuition. econstructor. apply H. trivial. trivial.
destruct IHtyp1 as (s1 & s2 & s3 & h). trivial. decompose [and] h; clear h.
exists s1; exists s2; exists s3; intuition.
eauto.
Qed.

Lemma Gen1c: forall  Γ A b T, Γ ⊢ λ[ A ], b : T -> exists B, 
  Γ ⊢' λ[A],b : Π ( A ), B /\ T ≡ Π ( A ), B /\ A::Γ ⊢ b : B.
intros.
remember ( λ[ A ], b) as L;  induction H; subst; try discriminate.
injection HeqL; intros; subst; clear HeqL.
exists B; eauto.
destruct IHtyp1; intuition.
exists x; eauto.
Qed.

(* seems useless since we inlined subst, same as above for var & app *)
Lemma Gen1e: forall M Γ T, Γ ⊢ M : T -> 
   (forall s, M <> !s) -> (forall A B, M <> Π(A),B) ->
   (forall A b, M <> λ[A],b) -> Γ ⊢' M : T.
induction 1; intros.
 elim(H1 s1); trivial.
 elim (H3 A B); trivial.
 elim (H3 A M); trivial.
 eauto.
 eauto.
 assert (Γ ⊢' M : A). apply IHtyp1; trivial.
 inversion H5; subst; clear H5.
  elim (H2 s1); trivial.
  elim (H3 A0 B0); trivial.
  elim (H4 A0 M0); trivial. 
  eauto. eauto.
Qed.
