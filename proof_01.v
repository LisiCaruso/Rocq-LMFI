(* 0 <> S(0)
you do that trought discriminate (tactic)

S(n) = S(p) -> n = p
you do that by injection (tactic)

H: a=b
rewrite H 
and it will replace every occourrence of a by b

rewrite <-H
it will replace every occourrence of b by a

x=y -> f(x) = f(y) 
tactic f equal *)

(** M2 LMFI : Internals of Coq basic logic *)

(* The only primitive stuff in Coq : universes and forall *)

(* the arrow (implication) is a notation for a non-dependent forall *)
Definition test (A B : Prop) := A -> B.

(*
Unset Printing Notations.
Print test.
*)

(* Logical constants : True *)

Print True.

(* Inductive True : Prop :=  I : True *)

Check I.

Lemma obvious : True.
(* exact I. *)
trivial. 
Show Proof.
(* constructor.
Show Proof. *)
Qed.

Lemma attempt : True -> True.
Proof.
 intros H.
 destruct H. (* no interesting elimination of H:True *)
Show Proof.
Abort.

Lemma attempt1 : True -> True.
Proof.
 intros H.
 apply H.
Abort.

(* False *)

Print False.
(* Inductive FalseBis : Prop := . *)

Print False_rect. (* elimination of False : a match with no branches
                     providing anything you want *)

Lemma false_elim : False -> 0 = 1.
Proof.
 intro H.
 destruct H.
 Show Proof.
Qed.

(* Negation : ~A shortcut A->False *)
(* the symbol ~ is on altgr + ì *)

(* Connectors : /\ and \/ *)

Print prod.  (* or * in the type_scope *)
Check (0,1).

Print and.
(*Inductive and (A B : Prop) : Prop := conj : A -> B -> and A B.
Print and_ind. *)

Lemma conj_intro : True /\ True.
Proof.
 split.
Show Proof. (* introduction is using constructor conj *)
trivial.
trivial.
Show Proof.
Qed.

Lemma conj_sym (A B : Prop) : A /\ B -> B /\ A.
Proof.
(*
 intuition.
Show Proof. (* an and_ind instead of a match, but that's equivalent *)
*)
 intros H.
 destruct H. Show Proof.
 auto.
Show Proof.
Qed.

(* disjonction : two constructors ! *)

Print or.
Check or.
Check or_introl. (* forall A B : Prop, A -> A \/ B *)
Check or_intror. (* forall A B : Prop, A -> A \/ B *)
Fail Check or_rect. (* no elimination on Type :
                       usually, no proofs can influence a program *)
(* Said again, the Prop world normally doesn't impact the program world
   : "proofs can be eliminated only to build proofs". *)
Fail Definition evade (p : True \/ True) : bool :=
 match p with
 | or_introl _ => true
 | or_intror _ => false
 end. (* Refused *)

Check or_ind. (* forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P *)
Print or_ind. (* a match on the proof of (A\/B) *)

(* the "left" tactic : applying the or_introl constructor *)
(*      right                       or_intror             *)
(*      destruct on a H:A\/B hypothesis : match H with ...*)

(* iff :   A<->B shortcut for (A->B)/\(B->A) *)

Lemma or_sym A B : A\/B -> B\/A.
Proof.
 intros [a|b]. (* same as intro H. destruct H. *)
 constructor. trivial. (* bad luck: tactic constructor takes the first
                          that fits. solution : constructor 2, or rather
                          left and right*)
Abort.

Lemma or_sym A B : A\/B -> B\/A.
Proof.
 intros [a|b]. (* same as intro H. destruct H. *)
 constructor 2. apply a. constructor. apply b. 
Qed. 

About "/\".
Locate "/\".

(* exists *)

Locate "exists". (* the underlying definition is called ex *)

(* exists x:A, P x  <-------> ex A P *)

Print ex.
(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall (x : A)(p : P x), ex A P.
*)
Print and.
(* 
Inductive and (A B : Prop) : Prop :=
    conj : A -> B -> A /\ B.
*)
(* Recall : "Logical pair" :

Inductive and (A B : Prop) : Prop :=
    conj : forall (a:A) (b:B),  and A B.
*)

(* in fact, ex is same, with a dependency on B (which becomes P ...)
   ex is a dependent pair (sigma type)
   : it groups a witness x and a proof of the property of x

   "introduce" : tactic called "exists ..." : internally apply of ex_intro
   "elimination" : destruct H when H:exists x,P x : that's a
     match H with
     | ex_intro x p => ...
     end.
*)

(* instead of "exists", you could try "econstructo"r (leave the witness
   undecided for the moment). See "eexists" also. Existential tactics
   (manipulating existential variables. *)

Lemma test_ex : exists n:nat, n = n.
Proof.
 eexists. (* ?n = ?n *)
Abort.

Print eexists.

(* eq *)

Print eq.

(* Syntactic equality : only x is equal to x *)
(*Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : eq A x x. *)
(* constructor is the reflexivity rule. tactic "reflexivity" *)

Lemma compute_equal : 2+2 = 4.
Proof.
 simpl.
 reflexivity.
Qed.

Check eq_ind.
(* The Leibniz principle, or the rewrite principle :
eq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
*)
(* match on a equality is a form of rewrite
   the rewrite tactic proceed by a match on the equality *)

Print eq_ind.

Lemma eq_sym A (x y : A) : x = y -> y = x.
Proof.
 intro H. destruct H. reflexivity.
Qed.
Print eq_sym.


(* nat and induction *)

Print nat.
Check nat_ind.
Print nat_ind. (* fixpoint + match *)

Lemma test_induction : forall n:nat, n=n.
induction n.
Show Proof.
Abort.

Print "+".
(*
2+2 = Nat.add (S (S 0)) 2.
    = match S (S 0) with
      | 0 => m
      | S p => S (add p 2)
     (* unfold rule for fixpoint : a fixpoint applied to a constructor can
        unfold once *)
    = S (add (S 0) 2)
    = ...
    = 4
*)
Compute 2+2.

Require Import Arith.
Check Nat.add_succ_l.

Lemma non_compute_proof : 2+2 = 4.
Proof.
 rewrite Nat.add_succ_l.
 rewrite Nat.add_succ_l.
 rewrite Nat.add_0_l.
 reflexivity.
Qed.
Print non_compute_proof.
Print Nat.add_succ_l.


Lemma compute_proof : 2+2 = 4.
(* in coq, most of the time we're modulo computation :
   2+2 just the same as 4 *)
 simpl. (* force a computation *)
 reflexivity.
Set Printing Implicit.
Show Proof.
Check (@eq_refl nat 4).
(* 2+2=4 and 4=4 are the *same* statement (modulo computation) :
    (what we call *convertible* )
   they can be proved by the *same* proof term *)
Qed.

Lemma compute_proof' : 2+2 = 4.
reflexivity.
Qed.

Definition compute_proof'' : 2+2 = 4 := eq_refl.
                                 (* or more precisely @eq_refl nat 4 *)

(* To be confirmed on recent Coq : issue with 8.12.0 ? *)


(* sig and sumbool : See later *)

Print sig. (* existential with output universe Type instead of Prop *)

Print sumbool. (* disjunction with output type in Type *)

