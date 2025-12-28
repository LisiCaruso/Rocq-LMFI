Require Import Bool Arith List.
Import ListNotations.
Set Implicit Arguments.

(* EXERCISE 1 : classical functions on lists *)

(* The inductive definition of lists, once again: *)
Print list.

(* Syntax about lists, provided by module ListNotations imported above *)
Check []. (* is equivalent to : nil *)
About "::". (* is equivalent to : cons *)

Check 1::[].

Check [1;2;3].
(* is equivalent to *)
Check 1::(2::(3::[])).

(* A first function on lists : length *)

Fixpoint length {A} (l:list A) :=
 match l with
 | [] => 0
 | x::q => S (length q)
 end.

Check @length.
Compute length [1;2;3].
Compute length [true;false;false].
Check [[1;2];[3];[];[5;6]].

(*Set Printing All. (*If you want to see all the implicit arguments*)*)
Check length [[1;2];[3];[];[5;6]].
Compute length [[1;2];[3];[];[5;6]].

(* Concatenation *)

Fixpoint app {A} (l1 l2 : list A) :=
 match l1 with
 | [] => l2
 | x1::q1 => x1 :: app q1 l2
 end.

Check app [1;2;3] [4;5].

(* Using Coq standard definition of app: *)
Check [1;2;3]++[4;5].

(* Reverse (in the "slow" definition, i.e. quadratic complexity) *)

Fixpoint rev {A} (l : list A) :=
 match l with
 | [] => []
 | x::q => rev q ++ [x]
 end.

(*
rev [1;2;3;4]
 = rev [1;2;3] ++ [4]
 = (rev [1;2]) ++ [3]) ++ [4]
 = (rev [1]) ++ [2]) ++ [3]) ++ [4]
 = ([] ++ [1]) ++ [2]) ++ [3]) ++ [4]
      cost 0  cost 1   cost 2  cost 3
 total cost proportional to (n*(n+1)/2) when n is length l
 i.e. quadratic
*)

(* Efficient reverse : we define first an auxiliary function called
   rev_app, which is almost app, but with the left list being reversed.*)

Fixpoint rev_app {A} (l1 l2 : list A) :=
 match l1 with
 | [] => l2
 | x1::q1 => rev_app q1 (x1::l2)
 end.

Compute rev_app [1;2;3] [4;5].

(* And then : *)

Definition fast_rev {A} (l:list A) := rev_app l [].

Compute fast_rev [1;2;3]. (* linear in the size of l *)

(* map and filter : pretty straightforward *)

Fixpoint map {A B} (f:A->B) l :=
 match l with
 | [] => []
 | x::q => f x :: map f q
 end.

Fixpoint filter {A} (f:A->bool) l :=
 match l with
 | [] => []
 | x::q => if f x then x :: filter f q else filter f q
 end.


(* fold *)

Compute fold_right Nat.add 0 [1;2;3]. (* sums all the numbers *)
Compute fold_left Nat.add [1;2;3] 0.  (* the same... *)

Check fold_right.
(* forall A B : Type, (B -> A -> A) -> A -> list B -> A *)

(* fold_right f a [x1;x2;x3] =
   (f x1 (f x2 (f x3 a))).
*)

Fixpoint fold_right {A B} (f:B->A->A) a l :=
 match l with
 | [] => a
 | x::q => f x (fold_right f a q)
 end.

Check fold_left.
(* : forall A B : Type, (A -> B -> A) -> list B -> A -> A *)

(* fold_left f [x1;x2;x3] a =
   f (f (f a x1) x2) x3.
*)

Fixpoint fold_left {A B} (f:A->B->A) l a :=
 match l with
 | [] => a
 | x::q => fold_left f q (f a x)
 end.

(* Let's use folds to rebuild a list *)

Compute fold_right (fun x l => x::l) [] [1;2;3].
Compute fold_left (fun l x => x::l) [1;2;3] [].

(* seq *)

Fixpoint seq start len :=
  match len with
  | 0 => []
  | S len' => start :: seq (S start) len'
  end.

(* head with the option type *)
Definition head {A} (l: list A) : option A :=
  match l with 
  | [] => None
  | x :: l' => Some x
 end.


Compute head [1;2;3].
Compute head [].

(* head with a default answer in the case of empty list *)
Definition head_dft {A} (l: list A) (dft : A) : A :=
  match l with 
  | [] => dft
  | x :: l => x
 end. 

Compute head_dft [1;2;3] 0.
Compute head_dft [] 0.

(* other approaches :
 - conditions ensuring that the list isn't empty
   (proof-carrying code, quite complex)
 - switch from list to a vector (list of a given size)
   head : vector A (S n) -> A
   (dependent-type programming)
*)
Fixpoint last {A} (l: list A) : option A :=
  match l with
  | [] => None
  | [a] => Some a
  | _::l => last l
 end. 

Fixpoint last_dft {A} (l: list A) (dft: A): A := 
  match l with 
  | [] => dft 
  | [a] => a
  | _::l => last_dft l dft
end.

Compute last [1;2;3].

Fixpoint nth_dft {A} (n:nat) (l : list A) (dft : A) : A :=
  match n, l with
  | _, [] => dft
  | 0, x::_ => x
  | S n, _::l => nth_dft n l dft  
 end.

Compute nth_dft 10 [1;2;3] 0.
Compute nth_dft 2 [1;2;3] 0.

Fixpoint nth {A} (n:nat) (l: list A) : option A :=
  match n, l with
  | _, [] => None
  | 0, x::_ => Some x
  | S n, _::l => nth n l
end.


Compute nth 10 [1;2;3].
Compute nth 2 [1;2;3].


(** EXERCISE 2 : executable predicates *)

(*
forallb : forallb {A}, (A->bool) -> list A -> bool. *)

Fixpoint forallb {A} (f:A->bool) l :=
 match l with
 | [] => true
 | x::q => f x && forallb f q
        (* or more lazy:
           if f x then forallb f q else false *)
 end.

(* increasing which tests whether a list of numbers is strictly increasing.*)

Fixpoint increasing (l : list nat) : bool :=
match l with 
| [] => true
| [x] => true
| x::((y::_) as q) => (x <?y ) && increasing q 
end. 

Compute increasing [1; 2; 3; 4; 5; 111].
Compute increasing [1; 2; 3; 7; 4; 5; 111].

(* Or in two steps (longer but more basic hence more robust) *)

Fixpoint larger_than x l :=
 match l with
 | [] => true
 | y::q => (x <? y) && larger_than y q
 end.

Definition increasing_v2 l :=
 match l with
 | [] => true
 | x::q => larger_than x q
 end.

(* Or more generic : *)

Fixpoint forallb_successive {A} (f:A->A->bool) l :=
 match l with
 | [] => true
 | [x] => true
 | x::((y::_) as q) => f x y && forallb_successive f q
 end.

Definition increasing' := forallb_successive Nat.ltb.
(* where Nat.ltb is the function behind the <? test *)

(* 
delta which tests whether two successive numbers of the list are always apart by at least k. *)
Compute 5-14.
Compute Nat.leb 5 3.

Fixpoint delta (l: list nat) k := 
  match l with 
   | [] => true 
   | [a] => true 
   | x::((y::l) as q) => (( k <=? (x-y) ) || ( k <=? (y-x) )) && delta q k
end. 

Definition delta' (k: nat) := forallb_successive (fun x y => (( k <=? (x-y) ) || ( k <=? (y-x) ))) .  

Compute delta' 1 [1;2;3;4].
Compute delta' 1 [1;2;3;3;4].
Compute delta' 2 [10;2;4].
Compute delta' 10 [10;20;30;45; 3].


Compute delta [1;2;3;4] 1.
Compute delta [1;2;3;3;4] 1.
Compute delta [10;2;3;4] 2.
Compute delta [10;20;30;45; 13] 10.

(** Mergesort *)

(*
Write a split function which dispatch the elements of a list into two lists of half the size (or almost). It is not important whether an element ends in the first or second list. In particular, concatenating the two final lists will not necessary produce back the initial one, just a permutation of it.
*)

Fixpoint split_at {A} (n: nat) (l : list A) :=
  match l, n with 
  | [], _ => ([], [])
  | l, 0 => ([], l)
  | a::x, S n => let (l1, l2):=split_at n x  in (a::l1, l2)
end. 

Compute split_at 0 [1;2;3;4].
Compute split_at 5 [1;2;3;4].
Compute 3/2.

Definition split {A} (l:list A) := split_at ((length l)/2) l.

Compute split [1;2;3;4;5].

Fixpoint split' {A} (l:list A) :=
 match l with
 | [] => ([], [])
 | x::q =>
   let (l1,l2) := split' q in
   (x::l2,l1)
 end.

Compute split' [1;2;3;4;5].


(* Write a merge function which merges two sorted lists into a new sorted list containing all elements of the initial ones. This can be done with structural recursion thanks to a inner fix (see ack in the session 3 of the course). *)

Fixpoint merge (l:list nat) : list nat -> list nat := 
  match l with 
  | [] => fun s => s
  | a::l' => fix merge_l s:=
              match s with 
              | [] => l
              | b::s' => 
                    if a<?b then a::(merge l' s)
                    else b::(merge_l s')
            end
end. 


Compute merge [1;3;4;5] [2;3;5;7].
Compute merge [10; 1; 1000] (merge [1;3;4;5] [2;3;5;7]).

(* Write a mergesort function based on the former functions.
*)

Fixpoint mergesort_counter l n :=
  match n with 
  | 0 => l
  | S n => match l with 
            | [] => []
            | [a] => [a]
            | _ => let (l1,l2) := split' l in
                       merge (mergesort_counter l1 n) (mergesort_counter l2 n)
           end
end.

Definition mergesort l := mergesort_counter l (length l).

Compute mergesort [1;7;2;3;10;0;3].


(* Write a powerset function which takes a list l and returns the list of all subsets of l.
For instance powerset [1;2] = [[];[1];[2];[1;2]]. The order of subsets in the produced list is not relevant. *)

Fixpoint powerset {A} (l: list A): list (list A):=
  match l with 
  | [] => [[]]
  | a::l' => let ll1:= powerset l' in
             ll1 ++ (map (fun l => a::l) ll1)
end.

Compute powerset [0; 1; 2].




