(** Exercise 3 : Fibonacci though matrices

Define a type of 2x2 matrices of numbers (for instance via a quadruple).
Define the multiplication and the power of these matrices.
Hint: the power may use an argument of type positive.
Define a fibonacci function through power of the following matrix: **)
Require Import NArith.


(* Inductive N : Set :=  N0 : N | Npos : positive -> N.
Arguments Npos _%positive_scope *)

Check (0%N, 0%N, 15%N).
Print N.of_nat.

Definition matrix_constr (a b c d : nat): N * N * N * N := (N.of_nat a, N.of_nat b, N.of_nat c, N.of_nat d).

Definition multmat u v :=
let '(u11, u12, u21, u22) := u in
let '(v11, v12, v21, v22) := v in
(u11*v11+u12*v21, u11*v12+u12*v22, 
u21*v11+u22*v21, u21*v12+u22*v22)%N.

Definition summat u v :=
  let '(u11,u12,u21,u22) := u in
  let '(v11,v12,v21,v22) := v in
  (u11+v11, u12+v12,
   u21+v21, u22+v22)%N.

Print positive.

Definition fibmat := (1,1,1,0)%N.

Print positive.

Fixpoint powmat m p :=
match p with 
  | 1 => m
  | p~0 => let m':= powmat m p in multmat m' m'
  | p~1 => let m':= powmat m p in multmat m (multmat m' m')
end%positive.


Fixpoint pow m p :=
  match p with 
  | 1 => m%positive
  | p~0 => let m' := pow m p in (m'*m')%positive
  | p~1 => let m' := pow m p in m*(m'*m')%positive
end%positive.

Compute pow 2 5.
Compute powmat fibmat 2.

Definition fib_mat n := let '(_, a, _, _):= powmat fibmat n in a.


Require Import Arith NArith List Bool.
Import ListNotations.
Compute List.map fib_mat [1;2;3;4;5;6;7;8;9;10]%positive.

Time Compute fib_mat (10000). (* 2s *)






