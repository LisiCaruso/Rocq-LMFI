(** We aim here at programming the Zeckendorf theorem in practice : every number can be decomposed in a sum of Fibonacci numbers, and moreover this decomposition is unique as soon as these Fibonacci numbers are distinct and non-successive and with index at least 2. **)


Require Import Arith NArith List Bool.
Import ListNotations.

(** Write a function fib_inv : nat -> nat such that if fib_inv n = k then fib k <= n < fib (k+1). **)

Fixpoint fib_inv_loop n a b k cpt :=
  match cpt with
  | 0 => 0
  | S cpt =>
    if n <? b then k
    else fib_inv_loop n b (a+b) (S k) cpt
end. 

Definition fib_inv n :=
 if n =? 0 then 0 else fib_inv_loop n 1 2 2 n.



Fixpoint fib_couple_loop (n: nat):nat*nat :=
  match n with 
  | 0 => (0, 0)
  | S 0 => (1, 0)
  | S (S m as m') => let p := fib_couple_loop(m') in
                        let a := fst p in 
                        let b := snd p in 
                     (a+b, a)
end.

Definition fib_fast (n: nat):nat := let '(a, b) := fib_couple_loop (n) in a.

Compute fib_inv 0.
Compute fib_inv 1.
Compute fib_inv 2.
Compute fib_inv 5.
Compute (fib_fast 5, fib_fast 6).
Compute fib_inv 10.
Compute (fib_fast 6, fib_fast 7).
Compute fib_inv 1000.
Compute (fib_fast 16, fib_fast 17).


