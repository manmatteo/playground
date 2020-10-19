Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Omega.
Require Import Bool.

Definition Sorts := nat.
Definition Vars := nat.

Inductive Term : Set:=
 | Var : Vars -> Term_List -> Term
 | Sort : Sorts -> Term
 | App : Term -> Term_List -> Term
 | Pi : Term -> Term -> Term
 | La :Term -> Term -> Term
with Term_List: Set :=
 | TNil : Term_List
 | TCons : Term -> Term_List -> Term_List
.

Notation "x ## l" := (Var x l) (at level 15, left associativity) : SC_scope.
Notation "t · l" := (App t l) (at level 15, left associativity) : SC_scope.
Notation "! s" := (Sort s) (at level 1) : SC_scope.
Notation "'Π' ( U ) , V " := (Pi U V) (at level 20, U, V at level 30) : SC_scope.
Notation "'λ' [ U ] , v " := (La U v) (at level 20, U , v at level 30): SC_scope.

Notation "[[]]" := TNil (at level 1) : SC_scope.
Notation "t ::: l" := (TCons t l) (at level 15, left associativity) : SC_scope.


Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity). 
Reserved Notation " l ↑↑ x # n " (at level 5, x at level 0, left associativity).

Open Scope SC_scope.

(* lift c n times *)
Fixpoint lift_rec (n:nat) (k:nat) (c':Term) {struct c'} := match c' with
   | x ## l =>  if le_gt_dec k x then (n+x) ## (l ↑↑ n # k) else x ## (l ↑↑ n # k)
   | ! s => ! s
   | t · l =>  (t ↑ n # k) · (l ↑↑ n # k)
   | Π ( A ), B => Π (A ↑ n # k), (B ↑ n # (S k))
   | λ [ A ], b => λ [A ↑ n # k], (b ↑ n # (S k)) 
 end  
   where "t ↑ n # k" := (lift_rec n k t) : SC_scope
with lift_rec_list (n:nat) (k:nat) (l:Term_List) {struct l} := match l with
  | [[]] => TNil
  | t ::: l' => (t ↑ n # k) ::: (l' ↑↑ n # k)
 end
  where "l ↑↑ n # k" := (lift_rec_list n k l) : SC_scope.

Notation " t ↑ n " := (lift_rec n 0 t) (at level 5, n at level 0, left associativity) : SC_scope.
Notation " l ↑↑ n " := (lift_rec_list n 0 l) (at level 5, n at level 0, left associativity) : SC_scope.

Scheme Term_ind' := Induction for Term Sort Prop
      with Term_List_ind' := Induction for Term_List Sort Prop.

Combined Scheme term_ind from Term_ind',  Term_List_ind'.

Lemma lift_rec_nil : forall l n m, [[]] = l ↑↑ n # m -> [[]] = l.
induction l; intros; simpl in |- *. 
trivial. discriminate.
Qed.

Lemma inv_lift : (forall t t' n m , t ↑ n # m = t' ↑ n # m -> t = t') /\ 
                 (forall l l' n m , l ↑↑ n # m = l' ↑↑ n # m -> l = l').
apply term_ind; intros.
induction t'; simpl in H0; try( destruct (le_gt_dec m v); discriminate).
simpl in H0.
destruct (le_gt_dec m v); destruct (le_gt_dec m v0); injection H0; intros; subst; clear H0.
rewrite (H t0 n m H1).
replace v with v0; trivial.
symmetry; apply plus_reg_l with n; trivial.
contradict g; intuition.
contradict g; intuition.
rewrite (H t0 n m H1); trivial.

induction t'; try discriminate.
simpl in H; destruct (le_gt_dec m v); discriminate.
simpl in H; trivial.

induction t'; try discriminate.
simpl in H1; destruct (le_gt_dec m v); discriminate.
simpl in H1. injection H1; intros; subst; clear H1.
rewrite (H t' n m H3). rewrite (H0 t1 n m H2); trivial.

induction t'; try discriminate.
simpl in H1; destruct (le_gt_dec m v); discriminate.
simpl in H1. injection H1; intros; subst; clear H1.
rewrite (H t'1 n m H3). rewrite (H0 t'2 n (S m) H2); trivial.

induction t'; try discriminate.
simpl in H1; destruct (le_gt_dec m v); discriminate.
simpl in H1. injection H1; intros; subst; clear H1.
rewrite (H t'1 n m H3). rewrite (H0 t'2 n (S m) H2); trivial.
(**)

simpl in H; trivial.
apply lift_rec_nil with n m; trivial.

destruct l'. simpl in H1. discriminate.
simpl in *.
injection H1; intros; subst; clear H1.
rewrite (H t1 n m H3); rewrite (H0 l' n m H2); trivial.
Qed.

Lemma lift_rec0 : (forall t n, t ↑ 0 # n = t) /\ (forall l n, l ↑↑ 0 # n = l).
apply term_ind; intros.
simpl. destruct (le_gt_dec n v). rewrite H. trivial. rewrite H. trivial.
simpl; trivial.
simpl; rewrite  H, H0; trivial.
simpl; rewrite  H, H0; trivial.
simpl; rewrite  H, H0; trivial.
simpl; trivial.
simpl; rewrite  H, H0; trivial.
Qed.

Lemma lift0 : (forall t, t ↑ 0 = t) /\ (forall l, l ↑↑ 0 = l)  .
destruct lift_rec0.
intuition.
Qed.

Lemma liftP1 : (forall t i j  k, (t ↑ j # i) ↑ k # (j+i) = t ↑ (j+k) # i) /\
               (forall l i j  k, (l ↑↑ j # i) ↑↑ k # (j+i) = l ↑↑ (j+k) # i).
apply term_ind; intros; simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec (j+i) (j+v)); simpl.
replace (k+(j+v)) with (j+k+v) by omega.  rewrite H. reflexivity.
contradict g; intuition.
simpl; destruct (le_gt_dec (j+i)); intuition.
contradict g; intuition.
rewrite H. trivial.
trivial.
rewrite H. rewrite H0. reflexivity.
rewrite H. replace (S(j+ i)) with (j+(S i)) by omega.  rewrite H0. reflexivity.
rewrite H. replace (S(j+ i)) with (j+(S i)) by omega.  rewrite H0. reflexivity.
trivial.
rewrite H. rewrite H0. trivial.
Qed.

Lemma liftP2: (forall t i j k n, i <= n -> (t ↑ j # i) ↑ k # (j+n) = (t ↑ k # n) ↑ j # i) /\
              (forall l i j k n, i <= n -> (l ↑↑ j # i) ↑↑ k # (j+n) = (l ↑↑ k # n) ↑↑ j # i).
apply term_ind; intros; simpl.
destruct (le_gt_dec i v); destruct (le_gt_dec n v).
simpl.
destruct (le_gt_dec (j+n) (j+v)); destruct (le_gt_dec i (k+v)).
rewrite H. replace (k+(j+v)) with (j+(k+v)) by intuition. trivial. trivial. 
contradict g; intuition.
contradict g; intuition.
contradict g; intuition.
simpl.
destruct (le_gt_dec (j+n) (j+v)); destruct (le_gt_dec i v).
contradict g; intuition.
contradict g; intuition.
rewrite H; trivial.
contradict g; intuition.
contradict g; intuition.
simpl.
destruct (le_gt_dec (j+n) v); (destruct (le_gt_dec i v)).
contradict g; intuition.
contradict g; intuition.
contradict g; intuition.
rewrite H; trivial.
trivial.
rewrite H;trivial;   rewrite H0;  trivial.
rewrite H;trivial;   replace (S(j+n)) with (j+(S n)) by intuition; rewrite H0;  intuition.
rewrite H;trivial;   replace (S(j+n)) with (j+(S n)) by intuition; rewrite H0;  intuition.
trivial.
rewrite H; trivial; rewrite H0; trivial.
Qed.

Lemma liftP3 : (forall t i k j n , i <= k -> k <= (i+n) -> (t ↑ n # i) ↑ j # k = t ↑ (j+n) # i) /\
               (forall l i k j n , i <= k -> k <= (i+n) -> (l ↑↑ n # i) ↑↑ j # k = l ↑↑ (j+n) # i).
apply term_ind; intros; simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec k (n+v)).
rewrite plus_assoc. rewrite H; trivial.
contradict g; intuition.
destruct (le_gt_dec k v); intuition.
contradict g; intuition.
rewrite H; trivial.
reflexivity.
rewrite H; intuition;rewrite H0; intuition.
rewrite H; intuition;rewrite H0; intuition.
rewrite H; intuition;rewrite H0; intuition.
trivial.
rewrite H; trivial; rewrite H0; trivial.
Qed.


Lemma lift_lift : forall t n m, (t ↑ m) ↑ n  = t↑ (n+m).
intros.
destruct liftP3; intuition.
Qed.

Lemma lift_lift_list : forall l n m, (l ↑↑ m) ↑↑ n  = l ↑↑ (n+m).
intros.
destruct liftP3; intuition.
Qed.

(* i = index to replace
  t = term we are replacing
 k = limit between free and bound indices
*)
Reserved Notation "t [ x ← u ]" (at level 5, x at level 0, left associativity).
Reserved Notation "l [[ x ← u ]]" (at level 5, x at level 0, left associativity).

Fixpoint subst_rec w t n {struct t} :=
 match t with
  | v ## l => match (lt_eq_lt_dec v n) with
      | inleft (left _) =>  v ## (l [[ n ← w ]])(* v < n *)
      | inleft (right _) => (w ↑ n) · (l[[ n ← w ]])  (* v = n *)
      | inright _ => (v - 1) ## (l [[ n ← w ]]) (* v > n *)
      end 
  | ! s => ! s
  | t · l => (t [ n ← w ]) · ( l [[ n ← w ]]) 
  | Π ( A ), B => Π ( A [ n ← w ] ), (B [ S n ← w ]) 
  | λ [ A ], b => λ [ A [ n ← w ] ], (b [ S n ← w ]) 
end
    where " t [ n ← w ] " := (subst_rec w t n) : SC_scope
 with subst_rec_list w l n {struct l} :=
 match l with
  | [[]] => [[]]
  | t ::: l' => (t [ n ← w ]) ::: (l' [[ n ← w ]])
end 
    where "l [[ n ← w ]]" := (subst_rec_list w l n) : SC_scope.


Notation " t [ ← w ] " := (subst_rec w t 0) (at level 5) : SC_scope.
Notation " l [[ ← w ]] " := (subst_rec_list w l 0) (at level 5) : SC_scope.


Lemma substP1:(forall t u i j k ,  ( t [ j ← u] ) ↑ k # (j+i) = (t ↑ k # (S (j+i))) [ j ← (u ↑ k # i ) ]) /\
              (forall l u i j k ,  ( l [[ j ← u]] ) ↑↑ k # (j+i) = (l ↑↑ k # (S (j+i))) [[ j ← (u ↑ k # i ) ]]).
apply term_ind; intros.
simpl ((v ## t) [j ← u] ↑ k # (j+i)).
change ((v##t) ↑ k # (S (j+i))) with  (if le_gt_dec (S (j+i)) v 
                                      then (k+v)## (t ↑↑ k # (S (j+i)))
                                      else v ##(t ↑↑ k # (S (j+i)))).
destruct (lt_eq_lt_dec v j). destruct s.
destruct (le_gt_dec (S (j+i)) v).
contradict l; intuition.
simpl.
destruct (le_gt_dec (j+i) v).
contradict l; intuition.
destruct (lt_eq_lt_dec v j).
destruct s. rewrite H. trivial.
contradict l; intuition.
contradict l; intuition.
destruct (le_gt_dec (S(j+i)) v). 
contradict l; intuition.
simpl.
destruct (lt_eq_lt_dec v j). 
destruct s.
contradict l; intuition.
destruct liftP2.  rewrite H0.  rewrite H. trivial. intuition.
contradict l; intuition.
destruct (le_gt_dec (S (j+i)) v).
simpl.
destruct (le_gt_dec (j+i) (v-1));
destruct (lt_eq_lt_dec (k+v) j).
destruct s.
contradict l; intuition.
contradict l; intuition.
replace (k+(v-1)) with (k+v-1) by omega.
rewrite H. reflexivity.
destruct s.
contradict l; intuition.
contradict l; intuition.
contradict l; intuition.
simpl.
destruct (le_gt_dec (j+i) (v-1)); destruct (lt_eq_lt_dec v j).
destruct s.
contradict l; intuition.
contradict l; intuition.
contradict l; intuition.
destruct s.
contradict l; intuition.
contradict l; intuition.
rewrite H. reflexivity.
simpl; trivial.
simpl; rewrite H; rewrite H0; intuition.
simpl; rewrite  H. replace (S(S(j+i))) with (S((S j)+i)) by omega. 
rewrite <- (H0 u i (S j)  k ); intuition. 
simpl; rewrite  H. replace (S(S(j+i))) with (S((S j)+i)) by omega. 
rewrite <- (H0 u i (S j)  k ); intuition. 
simpl; trivial.
simpl; rewrite H; rewrite H0; trivial.
Qed.

Lemma substP2: (forall t u i j n, i <= n -> (t ↑ j # i ) [ j+n ← u ] = ( t [ n ← u]) ↑ j # i) /\
               (forall l u i j n, i <= n -> (l ↑↑ j # i ) [[ j+n ← u ]] = ( l [[ n ← u]]) ↑↑ j # i).
apply term_ind; intros; simpl.
destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v n) .
destruct s.
simpl.
destruct (le_gt_dec i v);  destruct (lt_eq_lt_dec (j+v) (j+n)).
destruct s.
rewrite H; trivial.
contradict l; intuition.
contradict l; intuition.
contradict l; intuition.
contradict l; intuition.
simpl.
destruct (lt_eq_lt_dec (j+v) (j+n)).
destruct s.
contradict l; intuition.
symmetry.
destruct liftP3. rewrite H1; intuition. rewrite H; trivial.
contradict l; intuition.
simpl.
destruct (le_gt_dec i (v-1)); destruct (lt_eq_lt_dec (j+v) (j+n)).
destruct s.
contradict l; intuition.
contradict l; intuition.
rewrite H. replace (j+(v-1)) with (j+v-1) by intuition. trivial.
trivial.
destruct s.
contradict l; intuition.
contradict l; intuition.
contradict l; intuition.
destruct s.
simpl. destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v (j+n)).
destruct s.
contradict l; intuition.
contradict l; intuition.
contradict l; intuition.
destruct s.
rewrite H; trivial.
contradict l; intuition.
contradict l; intuition.
simpl.
destruct (lt_eq_lt_dec v (j+n)).
destruct s.
contradict l; intuition.
rewrite H; trivial.
replace j with 0 by intuition. simpl.
destruct lift_rec0.
rewrite H1. rewrite H2. trivial.
contradict l; intuition.
contradict l; intuition.
trivial.
rewrite H; trivial; rewrite H0; trivial.
replace (S(j+n)) with (j+(S n)) by omega; rewrite H; trivial; rewrite H0; intuition.
replace (S(j+n)) with (j+(S n)) by omega; rewrite H; trivial; rewrite H0; intuition.
trivial.
rewrite H; trivial; rewrite H0; trivial.
Qed.


Lemma substP3: (forall t u i  k n, i <= k -> k <= i+n -> (t↑ (S n) # i) [ k← u] = t ↑ n # i) /\
               (forall l u i  k n, i <= k -> k <= i+n -> (l ↑↑ (S n) # i) [[ k← u ]] = l ↑↑ n # i).
apply term_ind; intros; simpl.
destruct (le_gt_dec i v).
change (((S (n+v)) ## t ↑↑ (S n) # i) [k ← u]) with (
 match lt_eq_lt_dec  (S (n+v)) k with
  | inleft (left _ ) => (S(n+v)) ## ((t ↑↑ (S n) # i) [[ k ← u ]])
  | inleft (right _ ) => (u ↑ k) · ((t ↑↑ (S n) # i) [[ k ← u ]])
  | inright _ => (S(n+v)-1) ## ((t ↑↑ (S n) # i) [[ k ← u ]])
 end
).
destruct (lt_eq_lt_dec (S(n+v)) k).
destruct s.
contradict l;intuition.
contradict l;intuition.
rewrite H; trivial. replace  (S (n+v) -1) with  (n+v) by intuition; trivial.
simpl.
destruct (lt_eq_lt_dec v k).
destruct s.
rewrite H; trivial.
contradict g;intuition.
contradict l;intuition.
reflexivity.
rewrite H; trivial ; rewrite H0; trivial.
rewrite H; trivial ; rewrite H0; intuition.
rewrite H; trivial ; rewrite H0; intuition.
trivial.
rewrite H; trivial; rewrite H0; trivial.
Qed.


Lemma substP4: (forall t u w i j,(t [ i← u]) [i+j ← w] = (t [S(i+j) ← w]) [i← u[j← w] ]) /\
               (forall l u w i j,(l [[ i← u ]]) [[i+j ← w]] = (l [[S(i+j) ← w]]) [[i← u[j← w] ]]).
apply term_ind; intros; simpl.
destruct (lt_eq_lt_dec v i); destruct (lt_eq_lt_dec v (S(i+j))).
destruct s; destruct s0.
simpl.
destruct (lt_eq_lt_dec v (i+j)); destruct (lt_eq_lt_dec v i).
destruct s; destruct s0.
rewrite H. trivial.
contradict l; intuition. contradict l; intuition.
contradict l; intuition. contradict l; intuition.
contradict l; intuition. contradict l; intuition.
contradict l; intuition. 
simpl. destruct (lt_eq_lt_dec v i).
destruct s. contradict l; intuition.
rewrite H. destruct substP2. rewrite H0; intuition.
contradict l; intuition. contradict e; intuition.
destruct s. contradict l; intuition. contradict l; intuition.
destruct s.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)); destruct (lt_eq_lt_dec v i).
destruct s; destruct s0. 
contradict l; intuition. contradict l; intuition.
contradict l; intuition. contradict l; intuition.
destruct s. rewrite H; trivial.
contradict l; intuition. contradict l; intuition.
contradict l; intuition. simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)).
destruct s. contradict l; intuition.
destruct substP3. rewrite H0; intuition. rewrite H; intuition.
contradict l; intuition. simpl.
destruct (lt_eq_lt_dec (v-1) (i+j))  ; destruct (lt_eq_lt_dec (v-1) i).
destruct s; destruct s0. contradict l; intuition.
contradict l; intuition. contradict l; intuition.
contradict l; intuition. contradict l; intuition.
contradict l; intuition. rewrite H; trivial.

reflexivity.
rewrite H. rewrite H0. trivial.
rewrite H. replace (S (i+j)) with ((S i)+j) by intuition.  rewrite H0. trivial.
rewrite H. replace (S (i+j)) with ((S i)+j) by intuition. rewrite H0. trivial.

trivial.
rewrite H; rewrite H0; trivial.


Qed.

Lemma subst_travers : (forall  t N P n, (t [← N]) [n ← P] = (t [n+1 ← P])[← N[n← P] ]) /\
                      (forall  l N P n, (l [[← N]]) [[n ← P]] = (l [[n+1 ← P]])[[← N[n← P] ]]).
apply term_ind; intros; simpl.
destruct (lt_eq_lt_dec v 0); destruct (lt_eq_lt_dec v (n+1)).
destruct s; destruct s0.
contradict l; intuition. contradict l; intuition.
destruct lift0. rewrite H0. 
simpl.
destruct (lt_eq_lt_dec v 0).
destruct s.
contradict l0; intuition.
rewrite H0. rewrite H. trivial.
contradict l; intuition. contradict e; intuition.
destruct s. contradict l0; intuition. contradict l; intuition.
destruct s.
simpl.
destruct (lt_eq_lt_dec (v-1) n); destruct (lt_eq_lt_dec v 0).
destruct s; destruct s0.
contradict l2; intuition. contradict l; intuition.
contradict l1; intuition. contradict l; intuition.
destruct s. rewrite H; trivial.
contradict l0; intuition. contradict l0; intuition.
contradict l0; intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) n).
destruct s. contradict l; intuition.
rewrite H.
destruct substP3. replace (n+1) with (S n) by intuition. rewrite H0; intuition.
contradict l0; intuition.
simpl. 
destruct (lt_eq_lt_dec (v-1) n); destruct (lt_eq_lt_dec (v-1) 0).
destruct s; destruct s0.
contradict l2; intuition.
contradict l; intuition. contradict l1; intuition.
contradict e; intuition. contradict l; intuition.
contradict l; intuition. rewrite H; trivial.

trivial.
rewrite H; rewrite H0; trivial.
destruct substP4.
rewrite H. change (S n) with (1+n). rewrite H1. replace (n+1) with (1+n) by (apply plus_comm); trivial.
destruct substP4.
rewrite H. change (S n) with (1+n). rewrite H1. replace (n+1) with (1+n) by (apply plus_comm); trivial.

trivial.
rewrite H. rewrite H0. trivial.
Qed.

