(* How do the tactics discriminate and injection work internally ?
   ===============================================================
*)

Require Import List Nat Arith.

Import ListNotations.

Definition list_head {A} (l: list A) (default: A) :=
  match l with 
  | cons x l' => x
  | nil => default
end.

Definition list_tail {A} (l: list A):=
  match l with 
  | cons x l' => l'
  | nil => nil
end.

Lemma inject_head {A}: forall (x x': A) (l l' : list A),
    x::l = x'::l' -> x=x'.
Proof.
  intros.
  change (list_head (x::l) x = list_head(x'::l') x).
  rewrite H.
  reflexivity.
Qed.

Lemma inject_tail {A}: forall (x x': A) (l l': list A),
  x::l = x'::l' -> l = l'.
Proof.
  intros.
  change (list_tail (x::l) = list_tail (x'::l')).
  rewrite H.
  reflexivity.
Qed.
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


Lemma rev_emp {A: Type}: forall (l: list A), rev (l ++ []) = rev l.
Proof.
  intros. f_equal. apply nilAppR.
Qed.

Lemma rev_equal {A: Type}: forall (l: list A), rev l = rev_append l [] .
Proof.
  intros. unfold rev. reflexivity.
Qed.

(*
Show that length (rev l) = length l.
*)

Lemma length_append {A: Type}: forall (l: list A) (a: A), length(a::l) = S (length l).
Proof.
  intros. simpl. f_equal.
Qed.

Lemma add0R: forall (n: nat),n + 0 = n.
Proof.
  intros. auto.
Qed.

Lemma inject_length {A: Type}: forall (a b: list A), a=b -> length a = length b.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma rev_append_add {A: Type} (a b c: list A): 
  rev_append (a ++ b) c = rev_append b (rev_append a c).
Proof.
  revert c.
  induction a; intros; simpl.
  * reflexivity.
  * apply IHa. 
Qed.

Lemma rev_append_length {A} (l l' : list A) :
 length (rev_append l l') = length l + length l'.
Proof.
 revert l'. (* for turning l' back into a forall,
               and have later a IH starting with forall. *)
 induction l; simpl; auto.
 intros. rewrite IHl. simpl. apply Nat.add_succ_r.
Qed.

Lemma rev_length {A} (l : list A) : length (rev l) = length l.
Proof.
 unfold rev. rewrite rev_append_length. simpl. apply Nat.add_0_r.
Qed.

(*
Show that rev (l1 ++ l2) = (rev l2) ++ (rev l1).
*)


Lemma rev_append_app {A} (l1 l2 l' : list A) :
 rev_append (l1 ++ l2) l' = rev_append l2 (rev_append l1 l').
Proof.
 revert l'.
 induction l1.
 * simpl. auto.
 * simpl. intros. apply IHl1. 
Qed.

Lemma rev_append_rev_app {A} (l l' : list A) :
 rev_append l l' = rev l ++ l'.
Proof.
 revert l'.
 induction l; simpl; auto.
 intros. unfold rev. simpl. rewrite 2 IHl.
 rewrite <- app_assoc. reflexivity.
Qed.

Lemma rev_app {A} (l1 l2 : list A) :
 rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
 unfold rev at 1 3.
 rewrite rev_append_app.
 rewrite rev_append_rev_app.
 reflexivity.
Qed.

Fixpoint slow_rev {A} (l:list A) :=
 match l with
 | [] => []
 | x::l => slow_rev l ++ [x]
 end.


Lemma app_len {A} (l1 l2 : list A) :
 length (l1 ++ l2) = length l1 + length l2.
Proof.
 induction l1; simpl.
 - reflexivity.
 - now f_equal.  (* now is a tactic that solves basic proofs
                    (it calls a automatic tactic called "easy") *)
Qed.


Lemma slow_rev_length {A} (l : list A) : length (slow_rev l) = length l.
Proof.
 induction l; simpl; auto.
 rewrite app_len. simpl. rewrite Nat.add_1_r. now f_equal.
Qed.

Lemma slow_rev_app {A} (l1 l2 : list A) :
 slow_rev (l1 ++ l2) = slow_rev l2 ++ slow_rev l1.
Proof.
 induction l1; simpl; auto.
 - now rewrite nilAppR.
 - rewrite IHl1. now rewrite app_assoc.
Qed.



(* Extra exercice : prove that `slow_rev l = rev l` *)

Lemma slow_rev_rev {A} (l : list A) : slow_rev l = rev l.
Proof.
  induction l.
  * auto.
  * unfold rev. simpl. rewrite rev_append_rev_app. f_equal. apply IHl.
Qed.

(*
Lemma rev1 {A: Type}: forall (a: A), rev ([a]) = [a].
Proof.
  intros.
  reflexivity.
Qed.


Lemma rev_add {A: Type}: forall (l: list A) (a: A), rev (a::l)= (rev l)++[a]. 
Proof.
  intros.
  induction l.
  + simpl. reflexivity.
  + simpl. rewrite IHl.


Lemma rev_group {A: Type}: forall (l1 l2: list A), rev (l1 ++ l2) = (rev l2) ++ (rev l1). 
Proof.
  intros.
  induction l2.
  + simpl. f_equal. apply nilAppR.
  + simpl.  

Qed.

*) 

(** SPLIT *)

(* Here is two ways to dispatch elements of a list in two sub-lists of
 approximatively the same length. For instance split [1;2;3;4] = ([1;3],[2;4]). *)

Fixpoint split {A} (l:list A) :=
 match l with
 | [] => ([],[])
 | a::l => let (l1,l2) := split l in (a::l2,l1)
 end.

Fixpoint splitbis {A} (l:list A) :=
 match l with
 | [] => ([],[])
 | [a] => ([a],[])
 | a::b::l => let (l1,l2) := splitbis l in (a::l1,b::l2)
 end.

Compute split [1;2;3;4] .
Compute splitbis [1;2;3;4] .

(*
Lemma split_2 {A} (a b: A) (l: list A): split l = (l1, l2) -> splitbis (x :: a :: l) = 


split (x :: a :: l) =  splitbis (x :: a :: l)
*)

Lemma split_equiv_aux {A} (l:list A) :
  split l = splitbis l /\ forall x, split (x::l) = splitbis (x::l).
Proof.
  induction l.
  * split.
    + auto.
    + intros. simpl. reflexivity.
  * destruct IHl as (h1, h2). split.
    + apply h2.
    + intros. simpl. 
      destruct (splitbis l) as (l1,l2).
      rewrite h1. reflexivity.
Qed.

Lemma split_equiv {A} (l: list A): split l = splitbis l.
Proof.
  apply split_equiv_aux.
Qed.


Lemma split_contains {A} (l:list A) :
 let (l1,l2) := split l in
 forall x, In x l <-> In x l1 \/ In x l2.
Proof.
  induction l.
  * split.
    + intro.  left. apply H. 
    + intros [b | d]. apply b.  apply d.
  * simpl. destruct (split (a:: l)) as (l1, l2). 

    
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


