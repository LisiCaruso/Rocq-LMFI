(** Exercise 2: FIBONACCI **)

(* Define a function fib such that fib 0 = 0, fib 1 = 1 then fib (n+2) = fib (n+1) + fib n.
(you may use a as keyword to name some subpart of the match pattern ("motif" en français)).
*) 

Require Import Arith NArith List Bool.
Import ListNotations.



Fixpoint fib (n: nat):nat :=
  match n with 
  | 0 => 0
  | S 0 => 1
  | S (S m as m') => fib(m')+fib(m)
end.

Compute fib 6.

Definition fib_spec n := fib (n+2) =? fib n + fib (n+1).

Time Compute List.forallb fib_spec (List.seq 0 20).

 
(* Define an optimized version of fib that computes faster that the previous one by using Coq pairs.
*)

Print prod.

Definition fst' {A B} (p:A*B) := match p with
 | (a,b) => a
 end.

Definition fst {A B} (p:A*B) :=
 let '(a,b) := p in a.

Definition snd {A B} (p:A*B) :=
 let '(a,b) := p in a.

Compute fst (3,2).
Compute snd (3,2).


Fixpoint fib_couple_loop (n: nat):nat*nat :=
  match n with 
  | 0 => (0, 0)
  | S 0 => (1, 0)
  | S (S m as m') => let p := fib_couple_loop(m') in
                        let a := fst p in 
                        let b := snd p in 
                     (a+b, a)
end.

Fixpoint fib_couple_loop1 (n: nat):nat*nat :=
  match n with 
  | 0 => (0, 0)
  | S 0 => (1, 0)
  | S (m) => let '(a, b) := fib_couple_loop1(m) in 
                     (a+b, a)
end.

Definition fib_fast (n: nat):nat := let '(a, b) := fib_couple_loop1 (n) in a.

Compute fib_fast(10).
Compute fib(10).

Compute List.map fib_fast (List.seq 0 20).

(* Same question with just natural numbers, no pairs. Hint: use a special recursive style called "tail recursion". *)

Fixpoint fib_tail_loop (n a b: nat):nat :=
  match n with 
  | 0 => b
  | S n' => fib_tail_loop n' (a+b) a
end.

Definition fib_tail (n : nat):nat := fib_tail_loop n 1 0.

Compute fib_tail 10.


Time Compute (N.of_nat (fib 35)). (** une dizaine de secondes 7.52s*)
Time Compute (N.of_nat (fib_fast 35)). (** 6s *)
Time Compute (N.of_nat (fib_tail 35)).  (** 4s *)


(* Load the library of binary numbers via "Require Import NArith".
Adapt you previous functions for them now to have type nat -> N.
What impact does it have on efficiency ?
Is it possible to simply obtain functions of type N -> N ?
*)


Require Import NArith.

Print N.
(* Inductive N : Set :=  N0 : N | Npos : positive -> N.
Arguments Npos _%positive_scope *)

Print positive.
(*Inductive positive : Set :=
    xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Arguments xI _%positive_scope
Arguments xO _%positive_scope *)
Print Pos.add.
Check 0%N.
Fixpoint fibN (n:nat):N :=
    match n with 
    | 0 => 0%N
    | 1 => 1%N
    | S ( S n as p) => (fibN p + fibN n)%N
end.

Fixpoint fib_couple_loopN (n: nat): N*N :=
  match n with 
  | 0 => (0%N, 0%N)
  | S 0 => (1%N, 0%N)
  | S (S m as m') => let p := fib_couple_loopN(m') in
                        let '(a,b) := p in
                     ((a+b)%N, a)
end.

Definition fib_fastN (n: nat):N := let '(a, b) := fib_couple_loopN (n) in a.

Compute fib_fastN(100).
Compute fib_fastN(10).

Fixpoint fib_tail_loopN  (n: nat) (a b:N):N :=
  match n with 
  | 0 => b
  | S n' => fib_tail_loopN n' (a+b)%N a
end.

Definition fib_tailN (n : nat):N := fib_tail_loopN n 1%N 0%N.

Compute fib_tailN(100).
Compute fibN(10).
  

(** NB: le 10*1000 est pour éviter d'exploser le parser de nat,
    qui fait des "stack overflow" pour des constantes au dela
    de 5000. *)
(* Time Compute (fib_fastN 3500). (** 4s *) 
Time Compute (fib_tailN 3500).  (** 3.9s *) *)

(** Peut-on se passer complètement de [nat] ?
    Pas si simple alors de rester décroissant structurellement.
    On peut éventuellement utiliser [N.peano_rect]. *)

Check N.peano_rect.
Print Pos.peano_rect.

(** Le mystère de comment faire un [N.peano_rect] ?
    Cf [Print Pos.peano_rect] et voir qu'il est bien decroissant structurel *)

Definition fibNN2 n :=
  N.peano_rect
    _
    (0,1)%N
    (fun n p => let '(a,b) := p in (b,a+b)%N)
    n.

Definition fibNN n := fst (fibNN2 n).
(** Note: L'argument [_] caché dans [fibNN2] est [(fun _ => (N*N)%type)].
    Ce qui indique qu'on utilise [N.peano_rect] de façon *non-dépdendante*
    (les résultats ont toujours le même type, indépendemment de n).
*)
Compute List.map fibNN [0;1;2;3;4;5;6;7;8;9;10]%N.
Time Compute fibNN 10000. (* 29.778 secs *)

Definition fibNNloop n :=
 N.peano_rect
   _
   (fun a b => a)
   (fun _ p a b => p b (a+b)%N)
   n.

Definition fibNN_tail n := fibNNloop n 0%N 1%N.

Compute List.map fibNN [0;1;2;3;4;5;6;7;8;9;10]%N.

Time Compute fibNN_tail 10000. (* 31.53 secs *)










