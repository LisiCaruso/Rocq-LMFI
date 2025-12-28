(** Exercise 1:**)

(* usual functions on natural numbers
Load first the unary arithmetics : Require Import Arith.
If not done last week, define the following functions on nat (without using the ones of Coq standard library):

addition
multiplication
subtraction
factorial
power
gcd*)

Require Import Arith.

Fixpoint even (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => even n'
end.

Fixpoint mysum (n m: nat): nat :=
match n with 
| 0 => m
| S n' => S (mysum n' m)
end.

Compute mysum 3 4.
Compute mysum 10 344.

Fixpoint myproduct (n m: nat):nat :=
match n with
| 0 => 0
| S n' => mysum m (myproduct n' m)
end.

Compute myproduct 13 2.
Compute myproduct 4 7.

Definition mypred (n: nat):nat :=
match n with 
| 0 => 0
| S m => m
end.

Fixpoint mysubtraction (n m: nat):nat :=
match m with 
| 0 => n
| S m' => mypred (mysubtraction n m')
end.

Compute mypred 10.
Compute mypred 0.
Compute mysubtraction 130 20.

Fixpoint myfactorial (n: nat):nat :=
match n with
| 0 => 1
| S m => myproduct n (myfactorial m)
end.

Compute myfactorial 2.
Compute myfactorial 5.

Fixpoint mypower (n m: nat):nat :=
match m with 
| 0 => 1
| S m' => myproduct n (mypower n m')
end.

Compute mypower 2 3.
Compute mypower 1 10.
Compute mypower 2 10.

Fixpoint bigger (n m: nat): nat :=
  match n with 
  | 0 => m
  | S n' => match m with 
            | 0 => n
            | S m' => S (bigger n' m')
            end
end.

Fixpoint gcd1 (n m k:nat):nat :=
  match k with
  | 0 => 0
  | S k' => 
           if (bigger n m) =? n then 
                         if mysubtraction n m =? 0 then n
                         else gcd1 (mysubtraction n m) m k'
           else gcd1(mysubtraction m n) n k'
end.

Definition mygcd (n m:nat):nat := gcd1 n m (bigger n m).


Compute mygcd 3 6 .
Compute mygcd 100 3.
Compute mygcd 330 11.

Compute bigger 3 7.

Compute bigger 2 2.

(*define mymod *)

Fixpoint modulo_loop (a b n: nat):nat :=
  match n with 
  | 0 => 0
  | S n' => 
      if a <? b then a
      else modulo_loop (mysubtraction a b) b n'
end.

Definition modulo (a b: nat):nat := modulo_loop a b a.

Compute modulo 10 3.
Compute modulo 3 0.
Compute modulo 10 3.

Fixpoint gcd_loop (n m k: nat): nat :=
  match k with 
  | 0 => 0
  | S k' => if m =? 0 then n
            else gcd_loop m (modulo n m) k'
end.

Definition gcd n m := gcd_loop n m (bigger n m).

Compute gcd 3 6.
Compute gcd 100 3.
Compute gcd 330 11.






