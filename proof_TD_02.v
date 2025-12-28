(* nat_ind :
  forall P : nat -> Prop,
    P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Fixpoint add (n m:nat) : nat :=
  match n with
   | O => m
   | S p => S (add p m)
  end.

(*
 Show the following lemmas on addtion (basic equalities, then associativity and commutativity). Which egalities are "definitional" (obtained by mere computation and reflexivity, tactics simpl and reflexivity) ? For the other equalities, proceed by induction over n, thanks to the induction tactic.

*)

Lemma zero_zero : 0+0=0.
Proof.
trivial.
Qed.

Print eq_refl.

Lemma add_0_l : forall n, 0 + n = n.
Proof.
intros n.
trivial.
Qed.

Lemma add_succ_l : forall n m, S n + m = S (n + m).
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma add_0_r : forall n, n + 0 = n.
Proof.
  intros n.
  induction n.
  - apply zero_zero.
  - rewrite add_succ_l.
    f_equal.
    apply IHn.
Qed.

Lemma add_succ_r: forall n m, n + S m = S (n+m).
Proof.
  intros.
  induction n.
  - apply add_0_l.
  - simpl. f_equal. apply IHn.
Qed.

Lemma add_assoc : forall n m p, (n + m) + p = n + (m + p).
Proof.
intros.
induction n.
- reflexivity.
- simpl.
  f_equal.
  apply IHn.
Qed.

Lemma add_comm : forall n m, n + m = m + n.
Proof.
intros. 
induction n.
- simpl.
  rewrite add_0_r.
  reflexivity.
- rewrite add_succ_r.
  rewrite add_succ_l.
  f_equal.
  apply IHn.
Qed.

Fixpoint mul (n m:nat) : nat :=
  match n with
   | O => O
   | S p => m + mul p m
  end.

Lemma mul_0_l : forall n, 0 * n = 0.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma mul_succ_l : forall n m, S n * m = m + n * m.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma mul_0_r : forall n, n * 0 = 0.
Proof.
intros.
induction n.
- rewrite mul_0_l. reflexivity.
- simpl. apply IHn.
Qed.

Lemma add_ass_comm : forall a b c, a+(b+c) = b+(a+c).
Proof.
intros. 
induction a.
  * repeat rewrite add_0_l. reflexivity.
  * simpl. rewrite add_succ_r. f_equal. apply IHa.
Qed. 

Lemma mul_succ_r : forall n m, n * S m = n + n * m.
Proof.
intro n.
induction n.
- simpl. reflexivity.
- simpl. intro m. f_equal. rewrite IHn. rewrite add_ass_comm. reflexivity.
Qed.

Lemma subt_l : forall a b c, (b = c) -> (a+b=a+c).
Proof.
intros.  
rewrite H.
reflexivity.
Qed.

Lemma intermediate : forall a b c d, a + b + (c + d) = a + c + (b + d).
Proof.
intros. -
rewrite add_assoc. rewrite add_assoc. apply subt_l. rewrite add_ass_comm. reflexivity.
Qed. 

Lemma mul_distr : forall n m p, (n + m) * p = n * p + m * p.
Proof.
  intros.
  induction n.
  * rewrite mul_0_l. repeat rewrite add_0_l. reflexivity.
  * simpl. rewrite IHn. rewrite add_assoc. reflexivity.
Qed.



Lemma mul_distr' : forall n m p, (n + m) * p = n * p + m * p.
Proof.
intros.
induction n.
- reflexivity.
- simpl. rewrite IHn. 
  pose proof (add_assoc p (n*p) (m*p)) as H.
  symmetry in H.
  assumption.
Qed.

Lemma mul_assoc : forall n m p, (n * m) * p = n * (m * p).
Proof.
  intros.
  induction n.
  * repeat rewrite mul_0_l. reflexivity.
  * repeat rewrite mul_succ_l. rewrite mul_distr. rewrite IHn. reflexivity.
Qed.

Lemma mul_comm : forall n m, n * m = m * n.
Proof.
  intros.
  induction n.
  * simpl. rewrite mul_0_r. reflexivity.
  * simpl. rewrite mul_succ_r. rewrite IHn. reflexivity.
Qed.

(** Exercise 3 : an order relation on numbers **)
(*
Here is one possible way to define the large inequality on nat numbers:
*)

Definition le (n m : nat) := exists p, n + p = m.
Infix "<=" := le : alt_le_scope.
Open Scope alt_le_scope.
(*
Show that this predicate le is indeed an order relation:
*)
Lemma le_refl : forall n, n <= n.
Proof.
  intros.
  unfold le.
  exists 0.
  rewrite add_0_r.
  reflexivity.
Qed.

Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros.
  unfold le in *.
  destruct H as (q, H).
  destruct H0 as (r, H0).
  exists (q+r).
  rewrite <- add_assoc. rewrite H. rewrite H0. reflexivity.
Qed.


Lemma add_more_0 : forall n m, n+m = n -> m = 0.
Proof.
  intros.
  induction n.
  - rewrite add_0_l in H. apply H.
  - rewrite add_succ_l in H. injection H. apply IHn.
Qed.  

Lemma add_0_left_0 : forall n m, n+m = 0 -> n = 0.
 induction n; simpl; intros. (* ; easy finishes directly :-) *)
 - reflexivity.
 - discriminate.
Qed.

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
  unfold le.
  intros.
  destruct H as (p, H). destruct H0 as (q, H0).
  rewrite <- H in H0.
  rewrite add_assoc in H0.
  apply (add_more_0 n (p+q)) in H0.
  apply add_0_left_0 in H0.
  rewrite H0 in H.
  rewrite add_0_r in H.
  apply H.
Qed.

(*
Also show the following statements:
*)

Lemma le_succ : forall n m, n <= m -> n <= S m.
Proof.
  unfold le.
  intros n m (p, H).
  exists (S p).
  rewrite add_succ_r.
  f_equal.
  apply H.
Qed.

Lemma le_succ' : forall n m, n <= m -> n <= S m.
Proof.
 intros n m (q,H). exists (S q). rewrite add_succ_r. f_equal. apply H.
Qed.


Lemma le_total : forall n m, n <= m \/ m <= n.
Proof.
  induction n.
  + left. exists m. rewrite add_0_l. reflexivity.
  + destruct m.
    * right. exists (S n). rewrite add_0_l. reflexivity.
    * destruct (IHn m).
      - left. destruct H as (q,H). exists q. simpl. f_equal. assumption.
      - right. destruct H as (q, H). exists q. simpl. f_equal. apply H.
Qed.

(*
Note : this le definition is not the one used in the Coq standard library (cf. Init/Peano.v), which is based on an inductive predicate. But these two definitions are equivalent, you could even try to already prove that. Hint : a proof using a <= of Coq (internal name Peano.le) can be done by induction over this hypothesis.
*)

Close Scope alt_le_scope.
Locate "<=". (* Now <= is back to the default definition of Coq *)

Print Peano.le. (* The one of Coq : an inductive definition *)
(* 
Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n
  | le_S : forall m : nat,
           n <= m -> n <= S m.
*)

Lemma coq_le_add_r : forall n m, n <= n+m.
Proof.
 induction m.
 - rewrite add_0_r. apply Peano.le_n.
 - rewrite add_succ_r. apply Peano.le_S. assumption.
Qed.

Lemma le_equiv : forall n m, n <= m <-> le n m.
Proof.
 split.
 - intros H. induction H. (* induction on a inductive proof ! *)
   + apply le_refl.
   + apply le_succ; assumption.
 - intros (q,H). rewrite <- H. apply coq_le_add_r.
Qed.

