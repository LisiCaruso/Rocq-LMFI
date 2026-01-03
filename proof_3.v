Require Import List.
Import ListNotations.

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


Lemma my_inject_s: forall n m, S n = S m -> n = m.
Proof.
  intros.
  change (exhibit_succ (S n) = exhibit_succ (S m) ).
  rewrite H.
  f_equal.
Qed.

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

Print list.

Definition my_list_head {A} (l: list A) (default: A) :=
  match l with 
  | cons x l' => x
  | nil => default
end.

Definition my_list_tail {A} (l: list A):=
  match l with 
  | cons x l' => l'
  | nil => nil
end.

Definition proj1_cons {A} (l:list A) (default:A) :=
 match l with
 | cons x l => x
 | nil => default
 end.

Lemma my_inject_head {A}: forall (x x': A) (l l' : list A),
    x::l = x'::l' -> x=x'.
Proof.
  intros.
  change (my_list_head (x::l) x = my_list_head(x'::l') x).
  rewrite H.
  reflexivity.
Qed.

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


Lemma my_inject_tail {A}: forall (x x': A) (l l': list A),
  x::l = x'::l' -> l = l'.
Proof.
  intros.
  change (my_list_tail (x::l) = my_list_tail (x'::l')).
  rewrite H.
  reflexivity.
Qed.

Lemma inject_cons' {A}: forall (x x':A) l l',
    x::l = x'::l' -> l=l'.
Proof.
 intros.
 change (proj2_cons (x::l) = proj2_cons (x'::l')).
 rewrite H.
 reflexivity.
Qed.
