(*Exercise 2 --> Define without bool Define (without using bool 
nor any other inductive type):

-a type mybool : Type
-two constants mytrue and myfalse of type mybool
-a function myif : forall A, mybool -> A -> A -> A such that myif 
        mytrue x y computes to x and myif myfalse x y computes to y
*)

(*
Inductive mybool : Type :=
| top : mybool
| bottom : mybool.

(*altro modo 
Iductive mybool : Set := top | bottom
*)

Definition myneg : forall x : mybool, mybool := fun (x:mybool) => 
match x with
  | top => bottom
  | bottom => top
end.

Check myneg.
Compute (myneg top).
Check (myneg top).
*)

(*boolean is an evaluation function with a if *)

Definition mybool := forall X , X->X-> X.
(*if i use forall i'm talking about a type of functions*)
Check mybool.

Definition mytrue : mybool := fun _ x y => x.
Definition myfalse : mybool := fun _ x y => y.

(* DOMANDA IMPORTANTE: COME SCRIVO MYTRUE E MYFALSE SENZA _???
COME FACCIO A CAPIRE CHE MYTRUE E MYFALSE SONO DI TIPO MYBOOL???*)

Check mytrue.
Check myfalse.

Print mytrue.
Print myfalse.

Compute mytrue nat 1 2.
Compute myfalse nat 1 2.

(*- a function [myif : forall A, mybool -> A -> A -> A] such that 
 [myif mytrue x y] computes to [x] and [myif myfalse x y] computes to [y]. *)

Definition myif : forall {Y}(*sarebbe il tipo che si mangia per primo sia mytrue che myfalse*), mybool->Y->Y->Y :=
  fun _ b x y => b _ x y.

Compute myif mytrue 1 2.
Compute myif myfalse 1 2.












