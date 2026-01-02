(* How do the tactics discriminate and injection work internally ?
   ===============================================================
*)

Require Import List.

Import ListNotations.

(*
What is the type of app ?
*)
Fixpoint app {A:Type} (l1 l2 : list A) : list A :=
 match l1 with
 | [] => l2
 | x :: tl => x :: (app tl l2)
 end.
Check app.

(*
Show that for all lists l, we have nil ++ l = l and
l ++ nil = l.
Which of these two propositions corresponds to a definitional equality?
*)

Lemma nilAppL {A}: forall (l: list A), nil ++ l = l. 
Proof.
 trivial.
Qed.

Lemma nilAppR {A}: forall (l: list A), l ++ nil = l.
Proof.
  intros. 
  induction l.
  + trivial.
  + simpl. f_equal. apply IHl.
Qed.


(* Show that the concatenation is associative.
*)
 
Lemma ListConcAss {A}: forall (a b c: list A), (a ++ b) ++ c =  a ++ (b ++ c).
Proof.
  intros. 
  induction a.
  + simpl.  reflexivity.
  + simpl. f_equal. apply IHa.
Qed.

(* Define a function length : forall {A:Type}, list A -> nat
such that length l returns the length of the list l.
Check that your definition is indeed the same than the standard definition of Coq.
*)

Check 0.

Fixpoint length {A: Type} (l: list A) : nat :=
match l with 
  | [] => 0
  | a :: l => S (length l)
end.

Check list.
Print list.
Print Datatypes.length. (* how is done the standard definition of List.length ? *)

(*Show that length (l1 ++ l2) = length l1 + length l2
for all listes l1 and l2.*)

Lemma lengthGroup {A: Type}: forall (l1 l2: list A), length (l1 ++ l2) = length l1 + length l2.
Proof. 
  induction l1.
  simpl.
  + reflexivity.
  + simpl. intros. f_equal. apply IHl1.
Qed.

(* Reversing a list *)

(* Define a function rev : forall {A}, list A -> list A
reversing the list it receives. For that, you can introduce an
auxiliary function rev_append : forall {A}, list A -> list A -> list A
which reverse the first list and catenate it to the second one.
*)

Fixpoint rev_append {A} (a b: list A): list A:=
match a with
  | [] => b
  | x::a => rev_append a (x::b)
end.

Definition rev {A} (a: list A): list A := rev_append a [].

Compute rev [1; 3; 4].

(*
Show that length (rev l) = length l.
*)

Lemma length_append {A: Type}: forall (l: list A) (a: A), length(a::l) = S (length l).
Proof.
  intros. simpl. f_equal.
Qed.

Lemma length_rev {A: Type}: forall (l: list A), length (rev l) = length l.
Proof.
  intros.
  induction l.
  + simpl. reflexivity.
  + simpl.
Qed.

(*
Show that rev (l1 ++ l2) = (rev l2) ++ (rev l1).
*)


Lemma rev1 {A: Type}: forall (a: A), rev ([a]) = [a].
Proof.
  intros.
  reflexivity.
Qed.

Lemma rev_emp {A: Type}: forall (l: list A), rev (l ++ []) = rev l.
Proof.
  intros. f_equal. apply nilAppR.
Qed.

(*
Lemma rev_add {A: Type}: forall (l: list A) (a: A), rev (a::l)= (rev l)++[a]. 
Proof.
  intros.
  induction l.
  + simpl. reflexivity.
  + simpl. rewrite IHl.
*)

Lemma rev_group {A: Type}: forall (l1 l2: list A), rev (l1 ++ l2) = (rev l2) ++ (rev l1). 
Proof.
  intros.
  induction l2.
  + simpl. f_equal. apply nilAppR.
  + simpl.  

Qed.

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
