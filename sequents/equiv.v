Require Import dn_term.
Require Import dn_red.
Require Import dn_context.
Require Import dn_typ.
Require Import dn_sr.
Require Import sc_term. 
Require Import sc_red.
Require Import sc_context. 
Require Import sc_typ.
Require Import sc_sr.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.
Require Import List.
 
Open Scope SC_scope.

Fixpoint DN_to_SC_env (Γ: dn_context.Env) {struct Γ} : Env := match Γ with 
 | nil => nil
 | t::q => (DN_to_SC t) :: (DN_to_SC_env q)
end.

Fixpoint SC_to_DN_env (Γ: Env) {struct Γ} : dn_context.Env := match Γ with
 | nil => nil
 | t::q => (SC_to_DN t) :: (SC_to_DN_env q)
end.

Axiom Ax_eq : forall s t, Ax s t <-> dn_typ.Ax s t.
Axiom Rel_eq : forall s t u, Rel s t u <-> dn_typ.Rel s t u.

Hint Resolve Ax_eq Rel_eq.

Lemma DN_to_SC_List_reds_l : forall A l l', l ▹▹' l' -> DN_to_SC_List l A ▹▹ DN_to_SC_List l' A.
induction A; simpl; intros.
apply RBx_RT_Var. trivial.
apply RBx_RT_App; intuition.
eapply IHA1. apply RBx_RT_cons; intuition.
apply RBx_RT_App; intuition. 
apply RBx_RT_App; intuition.
Qed.


Lemma L204_3' : forall t , ((forall l l' ,(DN_to_SC_List l' t)·l ▹▹ (DN_to_SC_List l'@l t)) /\ (forall l,
  (DN_to_SC t) · l ▹▹ (DN_to_SC_List l t))).
induction t; split; intros; simpl.
apply RBx_RT_onestep. constructor. apply RBx_RT_onestep. constructor; simpl.

apply RBx_RT_onestep. constructor. constructor. 

destruct IHt1. apply H.
destruct IHt1. apply H.

apply RBx_RT_onestep. constructor. constructor.

apply RBx_RT_onestep. constructor. constructor.
Qed.


Lemma DN_to_SC_subst : forall A n b,  (DN_to_SC A) [n ← DN_to_SC b] ▹▹ DN_to_SC (A [n ← b])%DN
 with DN_to_SC_List_subst: forall A l n b , (DN_to_SC_List l A)[n ← DN_to_SC b] ▹▹ DN_to_SC_List (l [[n ← DN_to_SC b]]) (A [n ← b])%DN.
destruct A; intros; simpl.
destruct (lt_eq_lt_dec v n). destruct s. simpl. intuition.
rewrite DN_to_SC_lift. intuition.
simpl. intuition.
intuition.

eapply RBx_RT_trans2. apply DN_to_SC_List_subst. apply DN_to_SC_List_reds_l. simpl. apply RBx_RT_cons.
intuition. intuition.

apply RBx_RT_Pi; intuition.
apply RBx_RT_La; intuition.

destruct A; simpl; intros.
destruct (lt_eq_lt_dec v n). destruct s.
simpl. intuition.
rewrite <- DN_to_SC_lift. 
destruct L204_3' with (b ↑ n)%DN as (_ & ?).
apply H. 
simpl. intuition.
constructor; intuition.
eapply RBx_RT_trans2. apply DN_to_SC_List_subst. apply DN_to_SC_List_reds_l. simpl. apply RBx_RT_cons; intuition.

apply RBx_RT_App. apply RBx_RT_Pi; intuition. intuition.
apply RBx_RT_App. apply RBx_RT_La; intuition. intuition.
Qed.

Theorem SubRed_gen : forall Γ M F, Γ ⊢ M : F -> forall M', M ▹▹ M'-> Γ ⊢ M' : F.
intros. induction H0.
trivial.
apply IHRBx_RT.  destruct SubRed. eapply H2. apply H. trivial.
Qed.

Lemma L206_1' : forall (M M' : dn_term.Term) (N : Term),
       N = DN_to_SC M -> (M →→ M')%DN -> N ▹▹ (DN_to_SC M').
intros. generalize dependent N. induction H0; intros.
rewrite H; constructor.
apply RBx_trans_strict_flex. apply L206_1 with x; trivial.
eauto.
Qed.

Lemma Betac_to_RBx_RST : forall A B, (A ≡ B)%DN  -> (DN_to_SC A) ≡ (DN_to_SC B).
induction 1.
constructor.
apply L206_1' with x;trivial.
intuition.
eauto.
Qed.

Lemma item_DN_to_SC : forall Γ A v, (A  ↓ v ∈ Γ)%DN -> (DN_to_SC A) ↓ v ∈  (DN_to_SC_env Γ).
induction 1; simpl. constructor.
constructor. trivial.
Qed.

Lemma item_lift_DN_to_SC: forall Γ A v, (A ↓ v ⊂  Γ)%DN ->  (DN_to_SC A) ↓ v ⊂ (DN_to_SC_env Γ).
intros.
destruct H as (AA & ? & ?). exists (DN_to_SC AA); split.
rewrite H. rewrite DN_to_SC_lift. trivial.
apply item_DN_to_SC; trivial.
Qed.


Lemma item_SC_to_DN : forall Γ A v, A ↓ v ∈ Γ -> ((SC_to_DN A) ↓ v ∈ (SC_to_DN_env Γ))%DN.
induction 1; simpl. constructor.
constructor. trivial.
Qed.

Lemma item_lift_SC_to_DN: forall Γ A v, A ↓ v ⊂ Γ ->  ((SC_to_DN A) ↓ v ⊂ (SC_to_DN_env Γ))%DN.
intros.
destruct H as (AA & ? & ?). exists (SC_to_DN AA); split.
rewrite H. rewrite SC_to_DN_lift. trivial.
apply item_SC_to_DN; trivial.
Qed.

Lemma L218 : (forall Γ t T, (Γ ⊢ t : T)%DN -> 
 (forall C l, (DN_to_SC_env Γ) ; (DN_to_SC T)  ⊢ l :C -> (DN_to_SC_env Γ) ⊢ (DN_to_SC_List l t) : C) /\
 ( (DN_to_SC_env Γ) ⊢ (DN_to_SC t) : (DN_to_SC T) )) /\
 (forall Γ, (Γ ⊣)%DN ->  (DN_to_SC_env Γ) ⊣).
apply dn_typ.typ_induc; simpl; try split; intros.
(**)
econstructor. econstructor. destruct (Ax_eq s t). apply H2; trivial.
trivial. trivial.
(**)
constructor. destruct (Ax_eq s t); intuition. trivial.
(**)
econstructor. apply H0. apply item_lift_DN_to_SC; trivial.
(**)
apply item_lift_DN_to_SC in i.
assert (exists s, DN_to_SC_env Γ ⊢ DN_to_SC A : !s).
apply wf_item_lift in i; trivial. destruct H0 as (s & ?).
econstructor. econstructor. apply H0. trivial.
(**)
destruct H; destruct H0.
econstructor. econstructor. destruct (Rel_eq s t u). apply H5; trivial.
trivial. trivial. trivial.
(**)
destruct H; destruct H0.
econstructor. destruct (Rel_eq s t u). apply H4; trivial. trivial. trivial.
(**)
destruct H; destruct H0.
econstructor. econstructor. apply H2. trivial. trivial.
(**)
destruct H; destruct H0.
econstructor. apply H1. trivial.
(**)
destruct H; destruct H0.
assert (exists s, DN_to_SC_env Γ ⊢ Π (DN_to_SC B), DN_to_SC A : !s).
apply TypeCorrect in H2. destruct H2 as ( z & ?). destruct H2; try discriminate.
exists z; trivial.
destruct H4 as (sP & ?).
assert (exists s, (DN_to_SC B)::DN_to_SC_env Γ ⊢ DN_to_SC A : !s).
apply Gen1b in H4. destruct H4 as (s1 & s2 &s3 &h); intuition.
exists s2; trivial. destruct H5 as (sA & ?).
assert (DN_to_SC_env Γ ⊢ (DN_to_SC A)[ ← (DN_to_SC b)] : !sA).
change !sA with (!sA [← (DN_to_SC b)]). eapply cut4. apply H5.
apply H3. constructor. eapply wf_typ. apply H5.
apply H. apply typ_list_pi with sP. trivial. trivial.
eapply typ_list_conv_l. apply H1. apply H6.
apply RBx_RST_sym; constructor; apply DN_to_SC_subst.
(**)
destruct H; destruct H0.
assert (exists s, DN_to_SC_env Γ ⊢ Π (DN_to_SC B), DN_to_SC A : !s).
apply TypeCorrect in H1. destruct H1 as ( z & ?). destruct H1; try discriminate.
exists z; trivial.
destruct H3 as (sP & ?).
assert (exists s, (DN_to_SC B)::DN_to_SC_env Γ ⊢ DN_to_SC A : !s).
apply Gen1b in H3. destruct H3 as (s1 & s2 &s3 &h); intuition.
exists s2; trivial. destruct H4 as (sA & ?).
assert (DN_to_SC_env Γ ⊢ (DN_to_SC A)[ ← (DN_to_SC b)] : !sA).
change !sA with (!sA [← (DN_to_SC b)]). eapply cut4. apply H4. apply H2. constructor.
eapply wf_typ. apply H4.
assert (DN_to_SC_env Γ ⊢ DN_to_SC (A [ ← b])%DN : !sA).
eapply SubRed_gen. apply H5.
apply DN_to_SC_subst.
apply H. econstructor. apply H3. apply H2.
eapply typ_list_conv_l. econstructor. apply H6. apply H5.
apply RBx_RST_sym; constructor; apply DN_to_SC_subst.
(**)
destruct H; destruct H0.
apply H.
apply TypeCorrect in H2. destruct H2 as (sA & ?). destruct H2.
assert (DN_to_SC_env Γ ⊢ (DN_to_SC A) : !s).
apply Betac_to_RBx_RST in b. rewrite H2 in b. apply RBx_RST_sort in b.
eapply SubRed_gen. apply H3. rewrite H2; trivial.
apply typ_list_conv_l with (DN_to_SC B) s; trivial. apply RBx_RST_sym; apply Betac_to_RBx_RST; trivial.
apply typ_list_conv_l with (DN_to_SC B) sA; trivial. apply RBx_RST_sym; apply Betac_to_RBx_RST; trivial.
(**)
destruct H; destruct H0.
apply typ_conv with (DN_to_SC A) s; trivial. apply Betac_to_RBx_RST; trivial.
(**)
constructor.
(**)
destruct H.
apply wf_cons with s; trivial.
Qed.


Lemma L206_2_reds : forall M N, M ▹▹ N -> ((SC_to_DN M) →→ (SC_to_DN N))%DN . 
induction 1.
constructor.
eapply dn_red.Betas_trans. apply L206_2_aux. apply H.
trivial.
Qed.

Lemma L206_2_conv : forall M N, M ≡ N -> ((SC_to_DN M) ≡ (SC_to_DN N))%DN .
induction 1.
constructor; apply L206_2_reds; trivial.
intuition.
eauto.
Qed.

Lemma L219 : (forall Γ M A , Γ ⊢ M : A -> ((SC_to_DN_env Γ) ⊢ (SC_to_DN M) : (SC_to_DN A))%DN) /\
             (forall Γ B l A, Γ; B ⊢ l : A -> 
                   (forall t, ((SC_to_DN_env Γ) ⊢ t : (SC_to_DN B))%DN -> ((SC_to_DN_env Γ) ⊢ (SC_to_DN_List t l ) : (SC_to_DN A))%DN) /\ 
                   ((SC_to_DN_env Γ) ⊣)%DN /\
                   (exists s,(SC_to_DN_env Γ) ⊢ (SC_to_DN B) : !s)%DN) /\
             (forall Γ, Γ ⊣ -> ((SC_to_DN_env Γ) ⊣)%DN ).
apply typ_induc; simpl; intros.
(**)
econstructor. destruct (Ax_eq s1 s2); intuition. trivial.
(**)
econstructor. destruct (Rel_eq s1 s2 s3). apply H1; trivial. trivial.
trivial.
(**)
econstructor; eauto.
(**) 
destruct H as (? & ? & ? ). destruct H1 as (sA & ?). apply H. constructor. trivial. apply item_lift_SC_to_DN; trivial.
(**)
destruct H0 as (? & ? & ? ).
apply H0. trivial.
(**)
eapply dn_typ.Cnv. apply L206_2_conv. apply r. trivial. apply H0.
(**)
split; intros. trivial. split. eauto. exists s; trivial.
(**)
destruct H1 as (? & ? & ? ).
split; intros.
apply H1. rewrite SC_to_DN_subst. econstructor. apply H4. trivial. split. eauto.
exists s; trivial.
(**)
destruct H as (? & ? & ? ). split; intros.
eapply dn_typ.Cnv. apply L206_2_conv. apply r. intuition. apply H0. split. trivial. trivial.
(**)
destruct H as (? & ? & ? ). split; intros. destruct H2. 
apply H. eapply dn_typ.Cnv. apply L206_2_conv. apply RBx_RST_sym; apply r. trivial.
apply H2. split; trivial. exists s; trivial.
(**)
constructor.
(**)
econstructor. apply H.
Qed.

Lemma L219_2: forall Γ B l A, Γ; B ⊢ l : A -> forall t, ((SC_to_DN_env Γ) ⊢ t : (SC_to_DN B))%DN -> 
    ((SC_to_DN_env Γ) ⊢ (SC_to_DN_List t l ) : (SC_to_DN A))%DN.
intros.
destruct  L219.
destruct H2. eapply H2. apply H. trivial.
Qed.




