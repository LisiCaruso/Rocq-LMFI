(* How do the tactics discriminate and injection work internally ?
   ===============================================================
*)

Require Import List.
Import ListNotations.

(* discriminate : all inductive constructors are orthogonal *)

(* for nat : *)

Definition discr (m : nat) : Prop :=
 match m with
 | O => True
 | S _ => False
 end.

Compute discr 0. (* True *)
Compute discr 1. (* False *)

Lemma orthognal_S_O : forall n,  S n = 0 -> False.
(* said otherwise : forall n,  S n <> 0. *)
(* reminder : <> is the negation of = *)
(*            ~ A is A -> False *)
Proof.
 intros.
 (* discriminate. *)
 change (discr (S n)). (* convert the statement into something convertible*)
 rewrite H.
 simpl.
 constructor. (* or: exact I *)
Show Proof.
Qed.

(* for list *)

Definition discr_cons_nil {A}(l:list A) :=
 match l with
 | nil => True
 | cons _ _ => False
 end.

Lemma orthognal_cons_nil {A}: forall (x:A) l,  cons x l = nil -> False.
Proof.
 (* discriminate. *)
 intros.
 change (discr_cons_nil (cons x l)).
 rewrite H. constructor.
Qed.



(* injection : injectivity for free for any inductive constructor *)

(* for nat : *)

(* We need a projection of the first argument of S:
   That's the predecessor Nat.pred ! *)

Definition exhibit_succ (n:nat) : nat :=
 match n with
 | S x => x
 | O => O
 end.

Compute exhibit_succ 5. (* 4 *)

Lemma inject_S : forall n m,  S n = S m -> n = m.
Proof.
 intros.
(* injection H. *)
 change (exhibit_succ (S n) = exhibit_succ (S m)).
 rewrite H.
 reflexivity.
Show Proof.
Qed.

(* Same, for lists.
   First, a projection of the first argument of cons
   (We need a way to fill the other constructor, here nil,
    with something of the right type, here (default:A)
*)

Definition proj1_cons {A} (l:list A) (default:A) :=
 match l with
 | cons x l => x
 | nil => default
 end.

Lemma inject_cons {A}: forall (x x':A) l l',
    x::l = x'::l' -> x=x'.
Proof.
 intros.
 change (proj1_cons (x::l) x = proj1_cons (x'::l') x).
 rewrite H.
 reflexivity.
Qed.

(* Second, a projection of the second argument.
   Easier, no need for "default" this time. *)

Definition proj2_cons {A} (l:list A) :=
 match l with
 | cons x l => l
 | nil => nil
 end.


Lemma inject_cons' {A}: forall (x x':A) l l',
    x::l = x'::l' -> l=l'.
Proof.
 intros.
 change (proj2_cons (x::l) = proj2_cons (x'::l')).
 rewrite H.
 reflexivity.
Qed.
