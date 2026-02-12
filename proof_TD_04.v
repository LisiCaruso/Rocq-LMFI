Require Import Relations.
Print relation.
(* To shorten the types of (binary) relations: *)
(* relation T := T -> T -> Prop *)


Parameter T:Type.

Inductive clos1 (R : relation T) : relation T :=
| cl1_base : forall x y, R x y -> clos1 R x y
| cl1_refl : forall x, clos1 R x x
| cl1_trans : forall x y z, clos1 R x y -> clos1 R y z -> clos1 R x z.

Check clos1_ind.

(*
clos1_ind
     : forall (R : relation T) (P : T -> T -> Prop),
(forall x y : T, R x y -> P x y) ->
(forall x : T, P x x) ->
(forall x y z : T, clos1 R x y -> P x y -> clos1 R y z -> P y z -> P x z) ->
forall t t0 : T, clos1 R t t0 -> P t t0
*)

Definition Symmetric (R:relation T) := forall x y, R x y -> R y x.

Lemma clos1_sym R : Symmetric R -> Symmetric (clos1 R).
Proof.
    intros.
    unfold Symmetric in *.
    intros.
    induction H0.
    * apply cl1_base. apply H. apply H0.
    * apply cl1_refl.
    * eapply cl1_trans . apply IHclos1_2. apply IHclos1_1.
Qed.

Lemma clos1_idem : forall R, forall x y, clos1 (clos1 R) x y -> clos1 R x y.
    intros.
    induction H.
    * apply H.
    * apply cl1_refl.
    * eapply cl1_trans. apply IHclos1_1. apply IHclos1_2.  
Proof.

Inductive clos2 (R : T -> T -> Prop) : T -> T -> Prop :=
| cl2_refl : forall x, clos2 R x x
| cl2_next : forall x y z, clos2 R x y -> R y z -> clos2 R x z.

(* We will here show that these two definitions clos1 and clos2 are
actually equivalent. This can be done in the following intermediate steps:

Show that clos2 R x y implies clos1 R x y (for all x y:T).
Show that R x y implies clos2 R x y (for all x y:T).
Show that clos2 R is a transitive relation.
Conclude that clos1 R x y implies clos2 R x y (for all x y:T).
*)

Lemma clos2_then_clos1 : forall R : relation T, forall x y: T, 
clos2 R x y -> clos1 R x y.
Proof.
    intros.
    induction H.
    * apply cl1_refl.
    * eapply cl1_trans.
      apply IHclos2.
      apply cl1_base. apply H0.
Qed.

Lemma r_then_clos2 : forall R: relation T, forall x y: T, R x y -> clos2 R x y.
Proof.
    intros.
    eapply cl2_next. apply cl2_refl. apply H.
Qed.

Lemma clos2_trans : forall R: relation T, forall x y z : T,
clos2 R x y -> clos2 R y z -> clos2 R x z.
Proof.
    intros.
    induction H0.
    * apply H.
    * eapply cl2_next. 2: apply H1. apply IHclos2. apply H.
Qed.

Lemma clos1_then_clos2 : forall R : relation T, forall x y: T, 
clos1 R x y -> clos2 R x y.
Proof. 
    intros.
    induction H.
    * now apply r_then_clos2.  
    * apply cl2_refl.
    * eapply clos2_trans. apply IHclos1_1. apply IHclos1_2.
Qed.

(* Reflexive-transitive closure, version 3 *)

Definition identity : relation T := fun x y => x=y.
(* Or
Definition identity' : relation T := eq.
*)
Definition comp (R1 R2 : relation T) : relation T :=
 fun x z => exists y, R1 x y  /\ R2 y z.

Fixpoint pow (R:relation T) n : relation T :=
 match n with
 | O => identity
 | S n => comp (pow R n) R
 end.

 Definition clos3 (R : relation T) : relation T :=
 fun x y => exists n, pow R n x y.

Lemma clos3_clos2 R : forall x y, clos3 R x y -> clos2 R x y.
Proof.
    intros x y (n, H).
    revert x y H.
    induction n; simpl in *; intros x y.
    * unfold identity. intros. rewrite H. apply cl2_refl.
    * intros (u,(Hxu,Huy)). eapply cl2_next . apply IHn. apply Hxu. apply Huy. 
Qed.


Lemma clos2_clos3 R : forall x y, clos2 R x y -> clos3 R x y.
Proof.
    induction 1.
    * exists 0. unfold pow. reflexivity.
    * destruct IHclos2 as (n,IH). 
      exists (S n). simpl.
      exists y. split; assumption.
Qed.


(* Instance of always writing "forall x y, Foo x y <-> Bar x y",
   we could abstract that into an equivalence on relations : *)

Definition relequiv (R1 R2 : relation T) :=
 forall x y, R1 x y <-> R2 x y.

Infix "==" := relequiv (at level 70).

Lemma clos3_clos2_equiv R : clos3 R == clos2 R.
Proof.
 split. apply clos3_clos2. apply clos2_clos3.
Qed.

(* Extra question :
   Define pow in the other possible way :
    R^(n+1) = R.R^n instead of R^(n+1) = R^n.R
   And prove equivalent the two versions. *)

Fixpoint pow' (R:relation T) n : relation T :=
 match n with
 | O => identity
 | S n => comp R (pow' R n)
 end.

(* For working comfortably on ==, and especially be able
   to rewrite with it, let's first show it to be a setoid
   equivalence, compatible with composition comp. *)

Require Import Setoid Morphisms.

Instance : Equivalence relequiv.
Proof.
 split; try firstorder.
 intros R1 R2 R3 Eq1 Eq2 x y. now transitivity (R2 x y).
Qed.

Instance : Proper (relequiv ==> relequiv ==> relequiv) comp.
Proof.
 intros R1 R1' Eq1 R2 R2' Eq2.
 intros x y. split.
 - intros (u,(H1,H2)). exists u. now rewrite <- (Eq1 x u), <- (Eq2 u y).
 - intros (u,(H1,H2)). exists u. now rewrite (Eq1 x u), (Eq2 u y).
Qed.

(* Let's also prove a few basic laws of composition *)

Lemma comp_assoc R1 R2 R3 :
 comp (comp R1 R2) R3 == comp R1 (comp R2 R3).
Proof.
 split.
 - intros (u,((v,(H1,H2)),H3)).
   exists v. split; auto. now exists u.
 - intros (u,(H1, (v,(H2,H3)))).
   exists v. split; auto. now exists u.
Qed.

Lemma comp_id_r R : comp R identity == R.
Proof.
 intros x y. split.
 - now intros (u,(H,->)).
 - now exists y.
Qed.

Lemma comp_id_l R : comp identity R == R.
Proof.
 intros x y. split.
 - now intros (u,(->,H)).
 - now exists x.
Qed.

Lemma pow_S R n : pow R (S n) == comp R (pow R n).
Proof.
 induction n; simpl.
 - now rewrite comp_id_l, comp_id_r.
 - now rewrite <- comp_assoc, IHn.
Qed.

Lemma pow_equiv R n : pow R n == pow' R n.
Proof.
 induction n; simpl in *.
 - reflexivity.
 - now rewrite <- IHn, <- pow_S.
Qed.








    

