Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.
Require Import Bool.

Definition Sorts := nat.
Definition Vars := nat.

Inductive Term : Set:=
 | Var : Vars -> Term
 | Sort : Sorts -> Term
 | App : Term -> Term -> Term
 | Pi : Term -> Term -> Term
 | La :Term -> Term -> Term
.

Notation "x · y" := (App x y) (at level 15, left associativity) : DN_scope.
Notation "! s" := (Sort s) (at level 1) : DN_scope.
Notation "# v" := (Var v) (at level 1) : DN_scope.
Notation "'Π' ( U ) , V " := (Pi U V) (at level 20, U, V at level 30) : DN_scope.
Notation "'λ' [ U ] , v " := (La U v) (at level 20, U , v at level 30) : DN_scope.


Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity).

Delimit Scope DN_scope with DN. 

Open Scope DN_scope.

(* lift c n times *)
Fixpoint lift_rec (n:nat) (k:nat) (c':Term) {struct c'} := match c' with
   | # i =>  if le_gt_dec k i then Var (n+i) else Var i
   | ! s => Sort s
   | u · v=>  App (u ↑ n # k) (v ↑ n # k)
   | Π ( A ), B => Π (A ↑ n # k), (B ↑ n # (S k))
   | λ [ A ], b => λ [A ↑ n # k], (b ↑ n # (S k)) 
 end  
   where "t ↑ n # k" := (lift_rec n k t) : DN_scope.

Notation " t ↑ n " := (lift_rec n 0 t) (at level 5, n at level 0, left associativity) : DN_scope.


Lemma inv_lift : forall A B n m , A ↑ n # m = B ↑ n # m -> A = B.
intros A; induction A; destruct B; intros;
simpl in *; try (discriminate || intuition); (try (destruct (le_gt_dec m v) ; discriminate)).
destruct (le_gt_dec m v); destruct (le_gt_dec m v0); injection H; intros; subst; intuition.
injection H; intros; rewrite (IHA1 B1 n m H1); rewrite (IHA2 B2 n m H0); reflexivity.
injection H; intros; rewrite (IHA1 B1 n m H1); rewrite (IHA2 B2 n (S m) H0); reflexivity.
injection H; intros; rewrite (IHA1 B1 n m H1); rewrite (IHA2 B2 n (S m) H0); reflexivity.
Qed.

Lemma lift_rec0 : forall c n, c ↑ 0 # n = c.
induction c; intros; simpl.
destruct (le_gt_dec n v); reflexivity.
reflexivity.
rewrite IHc1; rewrite IHc2; reflexivity.
rewrite IHc1; rewrite IHc2; reflexivity.
rewrite IHc1; rewrite IHc2; reflexivity. 
Qed.

Lemma lift0 : forall c, c ↑ 0 = c .
intros; apply lift_rec0.
Qed.

Lemma liftP1 : forall t i j  k, (t ↑ j # i) ↑ k # (j+i) = t ↑ (j+k) # i.
intros t; induction t; intros;simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec (j+i) (j+v)); simpl.
replace (k+(j+v)) with (j+k+v) by omega; reflexivity.
intuition.
simpl; destruct (le_gt_dec (j+i)); intuition.
reflexivity.
rewrite IHt1;rewrite IHt2;reflexivity.
rewrite IHt1; rewrite <-IHt2 ;replace (j+S i) with (S(j+i)) by omega; reflexivity.
rewrite IHt1; rewrite <- IHt2 ;replace (j+S i) with (S(j+i)) by omega; reflexivity.
Qed.

Lemma liftP2: forall t i j k n, i <= n ->
  (t ↑ j # i) ↑ k # (j+n) = (t ↑ k # n) ↑ j # i.
intro t; induction t; intros; simpl.
destruct (le_gt_dec i v); destruct (le_gt_dec n v).
simpl.
destruct (le_gt_dec (j+n) (j+v)); destruct (le_gt_dec i (k+v)); intuition.
simpl.
destruct (le_gt_dec (j+n) (j+v)); destruct (le_gt_dec i v); intuition.
simpl.
destruct (le_gt_dec (j+n) v); destruct (le_gt_dec i (k+v)); intuition.
simpl.
destruct (le_gt_dec (j+n) v); (destruct (le_gt_dec i v)); intuition.
reflexivity.
rewrite IHt1; intuition;  rewrite IHt2; intuition;  reflexivity.
rewrite IHt1; intuition.
replace (S(j+n)) with (j+S n) by omega.
rewrite (IHt2 (S i) j k (S n)); intuition.
rewrite IHt1; intuition.
replace (S(j+n)) with (j+S n) by omega.
rewrite (IHt2 (S i) j k (S n) ); intuition.
Qed.

Lemma liftP3 : forall t i k j n , i <= k -> k <= (i+n) ->
  (t ↑ n # i) ↑ j # k = t ↑ (j+n) # i.
intro t; induction t; intros; simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec k (n+v)); intuition.
destruct (le_gt_dec k v); intuition.
reflexivity.
rewrite IHt1; intuition;rewrite IHt2; intuition.
rewrite IHt1; intuition;rewrite IHt2; intuition.
rewrite IHt1; intuition; rewrite IHt2; intuition.
Qed.


Lemma lift_lift : forall t n m, (t ↑ m) ↑ n  = t↑ (n+m).
intros.
apply liftP3; omega.
Qed.



(* i = index to replace
  t = term we are replacing
 k = limit between free and bound indices
*)
Reserved Notation "t [ x ← u ]" (at level 5, x at level 0, left associativity).

Fixpoint subst_rec w t n {struct t} :=
 match t with
  | # v => match (lt_eq_lt_dec v n) with
      | inleft (left _) => # v (* v < n *)
      | inleft (right _) => w ↑ n  (* v = n *)
      | inright _ => # (v - 1) (* v > n *)
      end
  | ! s => ! s
  | u · v => (u [ n ← w ]) · ( v [ n ← w ]) 
  | Π ( A ), B => Π ( A [ n ← w ] ), (B [ S n ← w ]) 
  | λ [ A ], b => λ [ A [ n ← w ] ], (b [ S n ← w ]) 
end
    where " t [ n ← w ] " := (subst_rec w t n) : DN_scope.


Notation " t [ ← w ] " := (subst_rec w t 0) (at level 5) : DN_scope.

Lemma expand_term_with_subst : forall B n, (B ↑ 1 # (S n)) [ n ← #0 ] = B.
induction B; intros.
unfold lift_rec.
destruct (le_gt_dec (S n) v).
unfold subst_rec.
destruct (lt_eq_lt_dec (1+v) n). destruct s.
apply le_not_lt in l.
elim l.
intuition.
apply le_not_lt in l. elim l; intuition.
change (1+v) with (S v). destruct v; simpl; trivial.
simpl.
destruct (lt_eq_lt_dec v n). destruct s.
trivial.
simpl; subst; trivial.
rewrite <- plus_n_O. trivial.
elim (lt_irrefl n); intuition.
simpl; trivial.
simpl.
rewrite IHB1. rewrite IHB2. reflexivity.
simpl. rewrite IHB1. rewrite IHB2. reflexivity.
simpl. rewrite IHB1. rewrite IHB2. reflexivity.
Qed.


Lemma substP1: forall t u i j k , 
  ( t [ j ← u] ) ↑ k # (j+i) = (t ↑ k # (S (j+i))) [ j ← (u ↑ k # i ) ].
intros t; induction t; intros.
simpl (#v [j ← u] ↑ k # (j+i)).
change (#v ↑ k # (S (j+i))) with  (if le_gt_dec (S (j+i)) v then #(k+v) else #v).
destruct (lt_eq_lt_dec v j). destruct s.
destruct (le_gt_dec (S (j+i)) v).
elim (lt_irrefl j); intuition.
simpl.
destruct (le_gt_dec (j+i) v).
elim (lt_irrefl j); intuition.
destruct (lt_eq_lt_dec v j).
destruct s.  reflexivity.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
destruct (le_gt_dec (S(j+i)) v). 
elim (lt_irrefl j); intuition.
simpl.
destruct (lt_eq_lt_dec v j). 
destruct s.
elim (lt_irrefl j); intuition.
apply liftP2; intuition.
elim (lt_irrefl j); intuition.
destruct (le_gt_dec (S (j+i)) v).
simpl.
destruct (le_gt_dec (j+i) (v-1));
destruct (lt_eq_lt_dec (k+v) j).
destruct s.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
replace (k+(v-1)) with (k+v-1) by omega.
reflexivity.
destruct s.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
simpl.
destruct (le_gt_dec (j+i) (v-1)); destruct (lt_eq_lt_dec v j).
destruct s.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
destruct s.
elim (lt_irrefl j); intuition.
elim (lt_irrefl j); intuition.
reflexivity.
intuition.
simpl; rewrite IHt1; intuition; rewrite IHt2; intuition.
simpl; rewrite IHt1; intuition.
replace (S(S(j+i))) with (S((S j)+i)) by omega.
rewrite <- (IHt2 u i (S j)  k ); intuition.
simpl; rewrite IHt1; intuition.
replace (S(S(j+i))) with ((S ((S j)+i))) by omega.
rewrite <- (IHt2 u i (S j)  k ); intuition.
Qed.

Lemma substP2: forall t u i j n, i <= n ->
  (t ↑ j # i ) [ j+n ← u ] = ( t [ n ← u]) ↑ j # i .
intro t; induction t; intros; simpl.
destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v n) .
destruct s.
simpl.
destruct (le_gt_dec i v);  destruct (lt_eq_lt_dec (j+v) (j+n)).
destruct s.
reflexivity.
elim (lt_asym v n); intuition.
intuition.
elim (lt_asym i v); intuition.
elim (lt_asym v n); intuition.
simpl.
destruct (lt_eq_lt_dec (j+v) (j+n)).
destruct s.
elim (lt_asym v n); intuition.
symmetry.
apply liftP3; intuition.
elim (lt_asym v n); intuition.
simpl.
destruct (le_gt_dec i (v-1)); destruct (lt_eq_lt_dec (j+v) (j+n)).
destruct s.
intuition.
elim (lt_asym v n); intuition.
intuition.
destruct s.
intuition.
elim (lt_asym v n); intuition.
intuition.
destruct s.
simpl.
destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v (j+n)).
destruct s.
intuition.
elim (lt_asym v n); intuition.
intuition.
destruct s.
intuition.
elim (lt_asym v n); intuition.
intuition.
simpl.
destruct (lt_eq_lt_dec v (j+n)).
destruct s.
elim (lt_asym v n); intuition.
elim (lt_asym v n); intuition.
elim (lt_asym v n); intuition.
simpl.
destruct (le_gt_dec i (v-1)); destruct (lt_eq_lt_dec v (j+n)).
destruct s.
intuition.
elim (lt_asym v n); intuition.
intuition.
destruct s.
intuition.
elim (lt_asym v n); intuition.
intuition.
intuition.
rewrite IHt1; intuition;rewrite IHt2; intuition.
rewrite IHt1; intuition;
rewrite <- (IHt2 u (S i) j (S n)); intuition.
replace (S(j+n)) with (j+(S n)) by omega.
reflexivity.
rewrite IHt1; intuition;
rewrite <- (IHt2 u (S i) j (S n)); intuition.
replace (S(j+n)) with (j+(S n)) by omega.
reflexivity.
Qed.


Lemma substP3: forall t u i  k n, i <= k -> k <= i+n ->
  (t↑ (S n) # i) [ k← u] = t ↑ n # i.
intro t; induction t; intros; simpl.
destruct (le_gt_dec i v).
change (#(S (n+v)) [k ← u]) with (
 match lt_eq_lt_dec  (S (n+v)) k with
  | inleft (left _ ) => #(S(n+v))
  | inleft (right _ ) => u ↑ k
  | inright _ => #(S(n+v)-1)
 end
).
destruct (lt_eq_lt_dec (S(n+v)) k).
destruct s.
intuition.
elim (lt_asym n v); intuition.
intuition.
simpl.
destruct (lt_eq_lt_dec v k).
destruct s.
reflexivity.
elim (lt_asym n v); intuition.
intuition.
reflexivity.
rewrite IHt1; intuition;rewrite IHt2; intuition.
rewrite IHt1; intuition; rewrite <- (IHt2 u (S i) (S k) n); intuition.
rewrite IHt1; intuition; rewrite <- (IHt2 u (S i) (S k) n); intuition.
Qed.

Lemma substP4: forall t u w i j, 
   (t [ i← u]) [i+j ← w] = (t [S(i+j) ← w]) [i← u[j← w]].
intro t; induction t; intros; simpl.
destruct (lt_eq_lt_dec v i); destruct (lt_eq_lt_dec v (S(i+j))).
destruct s; destruct s0.
simpl.
destruct (lt_eq_lt_dec v (i+j)); destruct (lt_eq_lt_dec v i); intuition ; 
  (try (elim (lt_asym v i); intuition)).
elim (lt_asym v i); intuition.
simpl.
destruct (lt_eq_lt_dec v i).
destruct s; intuition.
elim (lt_asym v i); intuition.
apply substP2; intuition.
elim (lt_asym v i); intuition.
elim (lt_asym v i); intuition.
destruct s.
elim (lt_asym v i); intuition.
elim (lt_asym v i); intuition.
destruct s.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)); destruct (lt_eq_lt_dec v i).
destruct s; destruct s0.
intuition.
elim (lt_asym v i); intuition.
elim (lt_asym v i); intuition.
elim (lt_asym v i); intuition.
destruct s.
reflexivity.
elim (lt_asym v i); intuition.
destruct s.
intuition.
elim (lt_asym v i); intuition.
intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)).
destruct s.
elim (lt_asym v i); intuition.
symmetry;apply substP3; intuition.
elim (lt_asym v i); intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j))  ; destruct (lt_eq_lt_dec (v-1) i).
destruct s; destruct s0.
reflexivity.
elim (lt_asym v i); intuition.
elim (lt_asym v i); intuition.
elim (lt_asym v i); intuition.
destruct s.
intuition.
elim (lt_asym v i); intuition.
destruct s.
intuition.
elim (lt_asym v i); intuition.
reflexivity.
reflexivity.
rewrite IHt1; rewrite IHt2; intuition.
rewrite IHt1; replace (S(S(i+j))) with (S((S i)+ j)) by omega;
  rewrite <- (IHt2 u w (S i)); replace (S(i+j)) with ((S i)+ j) by omega; intuition.
rewrite IHt1; replace (S(S(i+j))) with (S((S i)+j)) by omega;
  rewrite <- (IHt2 u w (S i)); replace (S(i+j)) with ((S i)+ j) by omega; intuition.
Qed.

Lemma subst_travers : 
 forall  M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]].
intro M; induction M; intros; simpl.
destruct (lt_eq_lt_dec v 0); destruct (lt_eq_lt_dec v (n+1)).
destruct s; destruct s0.
elim (lt_n_O v); intuition.
elim (lt_n_O v); intuition.
rewrite (lift0 N).
simpl.
destruct (lt_eq_lt_dec v 0).
destruct s.
elim (lt_n_O v); intuition.
rewrite (lift0 (subst_rec P N n)).
reflexivity.
elim (lt_n_O v); intuition.
rewrite e in e0. 
replace (n+1) with (S n) in e0.
discriminate e0.
omega. 
destruct s.
elim (lt_n_O v); intuition.
elim (lt_n_O (n+1)); intuition.
destruct s.
simpl.
destruct (lt_eq_lt_dec (v-1) n); destruct (lt_eq_lt_dec v 0).
destruct s; destruct s0.
elim (lt_n_O v); intuition.
elim (lt_irrefl 0); intuition. 
elim (lt_n_O v); intuition.
elim (lt_irrefl 0); intuition.
destruct s.
intuition.
elim (lt_n_O v); intuition.
destruct s.
elim (lt_n_O v); intuition.
elim (lt_irrefl 0); intuition.
intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) n).
destruct s.
elim (lt_asym v (n+1)); intuition.
destruct N.
simpl.
destruct (lt_eq_lt_dec v0 n).
destruct s.
replace (n+1) with (S n) by omega;  symmetry; apply substP3; intuition.
replace (n+1) with (S n) by omega; symmetry; apply substP3; intuition.
replace (n+1) with (S n) by omega; symmetry; apply substP3; intuition.
replace (n+1) with (S n) by omega; symmetry; apply substP3; intuition.
replace (n+1) with (S n) by omega; symmetry; apply substP3; intuition.
replace (n+1) with (S n) by omega;symmetry; apply substP3; intuition.
replace (n+1) with (S n) by omega;symmetry; apply substP3; intuition.
elim (lt_irrefl (n+1)); intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) n); destruct (lt_eq_lt_dec (v-1) 0).
destruct s; destruct s0.
intuition.
elim (lt_n_O n); intuition.
elim (lt_n_O n); intuition.
elim (lt_n_O n); intuition.
destruct s.
elim (lt_n_O n); intuition.
elim (lt_n_O n); intuition.
destruct s.
elim (lt_n_O n); intuition.
elim (lt_n_O n); intuition.
intuition.
intuition.
rewrite IHM1; rewrite IHM2 ; reflexivity.
rewrite IHM1; 
change (S n) with (1+n); rewrite substP4 ;replace (n+1) with (1+n) by (apply plus_comm); reflexivity.
rewrite IHM1; 
change (S n) with (1+n); rewrite substP4 ;replace (n+1) with (1+n) by (apply plus_comm); reflexivity.
Qed.

Lemma eta_related  : forall s t n m  k l , k+l <= m -> s ↑ n # m = t ↑ k # l -> 
  exists w, s = w ↑ k # l.
induction s; intros.
destruct t; try discriminate.
simpl in H0. 
destruct (le_gt_dec m v); destruct (le_gt_dec l v0).
exists (#(v-k)); simpl.
destruct (le_gt_dec l (v -k)).
intuition.
contradict g; intuition.
exists (#(v-k)); simpl.
destruct (le_gt_dec l (v -k)).
intuition.
contradict g; intuition.
rewrite H0.
exists #v0; simpl.
destruct (le_gt_dec l v0).
trivial.
contradict g0; intuition.
exists #v0; simpl.
destruct (le_gt_dec l v0). contradict g0; intuition.
trivial.
unfold lift_rec in H0; destruct (le_gt_dec m v); discriminate. 
unfold lift_rec in H0; destruct (le_gt_dec m v); discriminate. 
unfold lift_rec in H0; destruct (le_gt_dec m v); discriminate. 
unfold lift_rec in H0; destruct (le_gt_dec m v); discriminate. 
exists !s; simpl; trivial.
destruct t; try discriminate.
unfold lift_rec in H0; destruct (le_gt_dec l v); discriminate.
simpl in H0; injection H0; intros; subst; clear H0.
destruct (IHs2 t2 n m k l H H1); clear IHs2.
destruct (IHs1 t1 n m k l H H2); clear IHs1.
exists (x0· x); simpl; subst; trivial. 
destruct t; try discriminate.
unfold lift_rec in H0; destruct (le_gt_dec l v); discriminate.
simpl in H0; injection H0; intros; subst; clear H0.
destruct (IHs2 t2 n (S m) k (S l)); intuition; clear IHs2.
destruct (IHs1 t1 n m k l H H2); clear IHs1.
exists (Π(x0), x); simpl; subst; trivial. 
destruct t; try discriminate.
unfold lift_rec in H0; destruct (le_gt_dec l v); discriminate.
simpl in H0; injection H0; intros; subst; clear H0.
destruct (IHs2 t2 n (S m) k (S l));intuition;  clear IHs2.
destruct (IHs1 t1 n m k l H H2); clear IHs1.
exists (λ[x0],x); simpl; subst; trivial.
Qed. 


