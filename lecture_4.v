Fixpoint nbool (n: nat): Type :=
match n with
| 0 => bool
| S n => bool -> nbool n
end.

(*
Fixpoint nchecktauto (n: nat) : nbool n -> bool :=
match n with 
| 0 => fun b => b
| S n => fun f => nchecktauto (compose (nchecktauto n) f)
end. 

*)

Check (1,2,3).