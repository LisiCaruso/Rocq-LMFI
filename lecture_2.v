Require Import List.
Import ListNotations.

Fixpoint app {A} (l1 l2: list A):= 
  match l1 with 
    | [] => l2
    | a :: r1 => a :: (app r1 l2)
  end. 


Fixpoint revapp {A} (l1 l2: list A):= 
  match l1 with 
    | [] => l2
    | a :: r1 => revapp r1 (a :: l2)
  end. 

Definition rev {A} (l:list A) := 
  revapp l [].

Compute rev [1;2;3].


Fixpoint add n m := 
  match n with 
    | 0 => m
    | S n' => S (add n' m)
end. (* "head-recursive" mimicking peano axiom *)

Fixpoint add' n m :=
  match n with 
    | 0 => m
    | S n' => add' n' (S m)
end.  (*this is the tail-recursive style of programming*)

Definition pred (n: nat):nat :=
  match n with
    | 0 => 0 (*you can also use o the leter*)
    | S n' => n'
end. 

Definition pred_option (n : nat) : option nat :=
  match n with 
    | 0 => None 
    | S n' => Some n'
end.

Print option.

(*
Inductive
option (A : Type) : Type :=
    Some : A -> option A
  | None : option A.

Arguments option A%type_scope
Arguments Some {A}%type_scope a
  (where some original arguments have been renamed)
Arguments None {A}%type_scope

*)

Fixpoint nth_option {A} (n:nat) (l: list A) :=
  match n, l with 
    | _, [] => None
    | 0, x::_ => Some x
    | S n', _::l' => nth_option n' l'
  end.

Print nth_option.

(* nth_option = 
fix nth_option
  (A : Type) (n : nat) (l : list A) {struct n} :
    option A :=
  match n with
  | 0 =>
      match l with
      | [] => None
      | x :: _ => Some x
      end
  | S n' =>
      match l with
      | [] => None
      | _ :: l' => nth_option A n' l'
      end
  end
     : forall A : Type,
       nat -> list A -> option A

Arguments nth_option {A}%type_scope 
  n%nat_scope l%list_scope
*)








