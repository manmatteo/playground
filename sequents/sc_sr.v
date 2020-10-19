Require Import sc_term. 
Require Import sc_red.
Require Import sc_context. 
Require Import sc_typ.
Require Import List.


Reserved Notation "Γ ▹e Γ' " (at level 80, no associativity).

Inductive Beta_env : Env -> Env -> Prop :=
 | Beta_env_hd : forall A B Γ, A ▹ B -> A::Γ ▹e B::Γ
 | Beta_env_cons : forall A Γ Γ', Γ ▹e Γ' -> A::Γ ▹e A::Γ'
where "Γ ▹e Γ'" := (Beta_env Γ Γ') : SC_scope.

Hint Constructors Beta_env.

Lemma Beta_env_item_lift : forall Γ Γ' , Γ ▹e Γ'-> forall A v,  A ↓ v ⊂ Γ  ->
  (A ↓ v ⊂ Γ') \/ (exists B, A ▹ B /\ B ↓ v ⊂ Γ').
induction 1; intros.
destruct H0 as (AA & ? & ?). inversion H1; subst; clear H1.
right. exists (B↑ 1 ); split; intuition. exists B; intuition.
left. exists AA; intuition.
(**)
destruct H0 as (AA & ? &?). inversion H1; subst; clear H1.
left.  exists A;intuition.
destruct (IHBeta_env (AA↑(S n)) n). exists AA; intuition.
left. destruct H0 as ( B & ? & ?).
apply inv_lift in H0. exists AA; intuition.
constructor. rewrite H0; trivial.
destruct H0 as ( B & ? & ?).
right. exists (B↑ 1 ); split.
change (S (S n)) with (1+ (S n)). rewrite <- lift_lift. intuition.
destruct H1 as (BB & ? & ?).
exists BB; split. rewrite H1. rewrite lift_lift. trivial.
constructor; trivial.
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
apply IHitem; trivial. eapply wf_typ. apply H2.
Qed.

Lemma wf_item_lift : forall Γ t n ,Γ ⊣  -> t ↓ n ⊂ Γ ->
  exists s,  Γ ⊢ t  : !s.
intros.
destruct H0 as (u & ? & ?).
subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
eapply wf_item in H1.
destruct H1.
apply (@thinning_n (S n) Γ Γ' H) in H1.
exists x. simpl in H1. trivial.
trivial.
trivial.
trivial.
Qed.


Theorem SubRed_in_ctxt : (forall Γ M F, Γ ⊢ M : F -> forall Γ',  Γ' ⊣ -> Γ ▹e Γ'-> Γ' ⊢ M : F) /\
 (forall Γ C l D , Γ ; C ⊢ l : D -> forall Γ',  Γ' ⊣ -> Γ ▹e Γ'-> Γ'; C  ⊢ l : D) /\
 (forall Γ , Γ ⊣ -> True).
apply typ_induc; simpl; intros; trivial.
(**)
eauto.
(**)
econstructor; eauto.
(**)
econstructor; eauto. apply H0.
destruct (Gen1b Γ' A B !s)as (s1 &s2 & s3 & h); intuition. apply wf_cons with s1; trivial. intuition.
(**)
destruct (Beta_env_item_lift Γ Γ' H1 A v i).
apply typ_var with A. apply H ; trivial. trivial.
destruct H2 as (AA & ? & ?). 
apply typ_var with AA.
assert (exists s, Γ' ⊢ AA: !s).
apply wf_item_lift with v. eapply wf_typ_list. apply H. trivial. trivial. trivial.
destruct H4 as (sA & ?).  eapply typ_list_conv_l.  apply H ; trivial. apply H4. eauto. trivial.
(**)
eauto.
(**)
eauto.
(* list *)
eauto.
(**) eauto.
(**) eauto.
(**) eauto.
Qed.


Theorem SubRed : (forall Γ M F, Γ ⊢ M : F -> forall M', M ▹ M'-> Γ ⊢ M' : F ) /\
                 (forall Γ H l F, Γ ; H ⊢ l : F -> forall l',l ▹' l' ->  Γ ; H ⊢ l' : F) /\ 
                 (forall Γ, Γ ⊣ -> True).
destruct SubRed_in_ctxt as (S1 & S2 & _).
apply typ_induc; try split; intros.
(**)
inversion H0.
(**)
inversion H1; subst; clear H1.
eauto. econstructor. apply r. intuition. eauto.
(**)
inversion H1; subst; clear H1.
eauto. econstructor. econstructor.
apply H. eauto. eapply S1. apply t0.
destruct (Gen1b Γ B0 B !s)as (s1 &s2 & s3 & h); intuition. apply wf_cons with s1; trivial. intuition.
apply t. eauto.
(**)
inversion H0; subst; clear H0. eauto.
(**)
inversion H1; subst; clear H1.
 apply Gen1c in t. destruct t as (B0 & ? & ? & ?).
 apply Gen2b in t0. destruct t0 as (A1 & B1 & h); decompose [and] h; clear h.
 assert (exists s, Γ ⊢ A0: !s).
 apply wf_typ in H3. destruct H3. apply wf_inv in H3. intuition. destruct H7 as (sA & ?).
 assert (exists s, A0::Γ ⊢ B0: !s).
 inversion H1; subst; clear H1. apply Gen1b in H13. destruct H13 as (s1 & s2 & s3 & h); decompose [and] h; clear h.
 exists s2; trivial. destruct H9 as (sB & ?). 
 destruct (RBx_RST_to_Pi A0 B0 A1 B1). eauto.
 apply typ_app with (B0[ ← v]). apply cut4 with (A0::Γ) Γ A0; trivial.
 apply typ_conv with A1 sA; trivial. intuition. eauto.
 apply typ_list_conv_l with (B1 [ ← v]) sB; trivial.
 change !sB with !sB[ ← v]. apply cut4 with (A0::Γ) Γ A0; trivial.
 apply typ_conv with A1 sA; trivial. intuition. eauto. 
 apply RBx_RST_subst. intuition.
  
 assert (exists s, Γ ⊢ B : !s). apply TypeCorrect_list in t0. trivial.  destruct H1 as (sB & ?).
 apply Gen2a in t0.
 apply typ_conv with A sB; trivial. intuition.

 apply Gen1e in t. inversion t; subst; clear t.
 apply typ_var with A0; trivial. apply cut1 with A; trivial.
 intros; intro; discriminate.  intros; intro; discriminate.  intros; intro; discriminate.


 apply Gen1e in t. inversion t; subst; clear t.
 apply typ_app with A0; trivial. apply cut1 with A; trivial.
 intros; intro; discriminate.  intros; intro; discriminate.  intros; intro; discriminate.

 eauto. eauto.
(**)
eauto.
(* list *)
inversion H0.
(**)
inversion H2; subst; clear H2. econstructor. apply t. eauto. 
assert (exists s, A::Γ ⊢ B : !s). apply Gen1b in t. destruct t as (s1 & s2 &s3 & h); decompose [and] h; exists s2; trivial.
destruct H2 as (sB & ?).
apply typ_list_conv_l with( B [ ← M]) sB; trivial. 
change !sB with !sB[ ← t']. eapply substitution. apply H2. apply H0. trivial. constructor.
eapply wf_typ. apply H2.  apply RBx_RST_subst2. eauto.
econstructor. apply t. trivial. apply H1. trivial.
(**)
eauto.
(**)
eauto.
Qed.

