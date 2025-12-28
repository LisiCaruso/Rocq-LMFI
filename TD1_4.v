(*Exercise 4 : Booleans

Write a function checktauto : (bool->bool)->bool which tests whether a Boolean unary function always answers true.

Same for checktauto2 and checktauto3 for Boolean functions expecting 2, then 3 arguments. This can be done by enumerating all cases, but there is a clever way to proceed (for instance by re-using checktauto.
*)
Require Import Bool. 
Print bool.

Definition checktauto1 (f: bool -> bool):bool :=
(f true) && (f false).

Compute checktauto1 negb.
(*Definition checktauto : ((bool->bool)->bool) := fun R : bool->bool => andb (R true) (R false). *)

Definition checktauto2 (f: bool -> bool -> bool): bool := checktauto1(f true) && checktauto1(f false).

Definition checktauto3 (f: bool -> bool -> bool -> bool):bool := checktauto2(f true) && checktauto2(f false).

(*Definition checktauto2 : ( (bool->bool-> bool)-> bool ) := fun R : bool -> bool -> bool  => checktauto1(R true) && checktauto1(R false).

Definition checktauto3 : ( (bool->bool-> bool -> bool )-> bool ) := fun R : bool -> bool -> bool -> bool  => checktauto2(R true) && checktauto2(R false). *)

Definition f (a b c: bool):bool := a || b || c || negb (a && b) || negb (a && c).


Compute checktauto3 f.

Fixpoint factorial (n:nat) :=
 match n with
 | 0 => 1
 | S m => (factorial m) * n
 end.
(*Check whether fun a b c => a || b || c || negb (a && b) || negb (a && c) is a tautology.
Note : the command Open Scope bool_scope. activates notations || and && (respectively for functions orb and andb).*)
Definition f1 := fun a b c => a || b || c || negb (a && b) || negb (a && c).
Compute checktauto3 f1.

(*Define some functions behaving like Coq standard functions negb and orb and andb.
*)

Definition myneg (x: bool):bool := match x with 
| true => false
| false => true
end.

Definition myor (a b : bool):bool := match a, b with
| true, true => true
| true, false => true
| false, true => true 
| false, false => false
end.

Definition myor2 (a b : bool):bool := match a with
| true  => true 
| false => match b with 
          | true => true 
          | false => false
          end
end.


Definition myand (a b : bool): bool := match a, b with
                                        | true, true => true
                                        | _, _  => false
end. 
Compute myneg true.
Compute myor true false.
Compute myor2 false false.
Compute myand true false.