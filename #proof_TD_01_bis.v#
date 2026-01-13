(*
Some more tactics
In Coq, a definition d could be replaced by its body thanks to the tactic "unfold d".

The equality is handled by tactics "reflexivity" and "symmetry" and "transitivity ..." (give the intermediate term) and "rewrite ..." (give the equality name or lemma to use as a rewrite rule) or "rewrite <- ..." (right-to-left rewriting).
*) 

(** Exercise 1 : Order relations **)
Module Exercise1. 

(* Let's consider a type E:Type equipped by a binary relation R supposed to satisfy the axioms of order relations: *)

Parameter E : Type.
Parameter R : E -> E -> Prop.
Axiom refl : forall x : E, R x x.
Axiom trans : forall x y z : E, R x y -> R y z -> R x z.
Axiom antisym : forall x y : E, R x y -> R y x -> x = y.


(* We define the notion of smallest and minimal elements this way: *)

Definition smallest (x0 : E) := forall x : E, R x0 x.
Definition minimal (x0 : E) := forall x : E, R x x0 -> x = x0.


Check smallest.
Check minimal.
(* What are the types of smallest and minimal ? *)
(* smallest: E -> Prop. 
   minimal : E -> Prop.
*) 

(*
State in Coq and prove the following lemmas:

If R admits a smallest element, this one is unique.
The smallest element, if it exists, is a minimal element.
If R admits a smallest element, then there is no other minimal element that this one. *)

(* If R admits a smallest element, this one is unique. *)
Lemma smallest_unique: forall x, forall y, (smallest x /\ smallest y) -> x=y.
Proof.
  intros x y.
  intros.
  destruct H as (sx, sy).
  unfold smallest in *.
  apply antisym.
  apply sx.
  apply sy.
Qed.

Lemma E1Q1 :
 forall x x', smallest x -> smallest x' -> x=x'.
Proof.
 intros x x' Hx Hx'.
 unfold smallest in *.
 apply antisym.
 apply Hx.
 apply Hx'.
Qed.


(*The smallest element, if it exists, is a minimal element.*)
Lemma smallest_minimal: 
  forall x, smallest x -> minimal x.
Proof.
  intros x sx.
  unfold smallest in sx.
  unfold minimal.
  intros y. 
  intros H.
  apply antisym.
  apply H. 
  apply sx.
Qed.

Lemma E1Q2 :
 forall x, smallest x -> minimal x.
Proof.
 intros x Hx.
 unfold smallest in *. unfold minimal.
 intros x' Hx'.
 apply antisym.
 apply Hx'.
 apply Hx.
Qed.

(* If R admits a smallest element, then there is no other minimal element that this one. *)
Lemma E1Q3 : 
  forall x, smallest x -> forall y, minimal y -> x=y.
Proof.
  intros x sx y my.
  unfold smallest in sx.
  unfold minimal in my.
  apply my.
  apply sx.
Qed. 

End Exercise1.

Module Exercise2.
(** Exercice 2 : Classical logic **)
(*
In this exercise, we assume the reasoning rule "by absurdum", that we can declare in Coq via:
*)
Axiom not_not_elim : forall A : Prop, ~~A -> A.
(*
Show in Coq that this axiom implies the excluded-middle : forall A : Prop, A \/ ~ A.
*)

Lemma EM : forall A, A\/~A.
Proof.
 intros A.
 apply not_not_elim.
 intro H. apply H. right.
 intro. apply H. left. assumption.
Qed.



Lemma exm : forall A:Prop, A\/~A.
Proof.
  intro A.
  apply not_not_elim.
  intro H.
  apply H.
  right.
  intro A1.
  apply H. 
  left.
  apply A1.
Qed.

(*
We now aim at proving the drinker's paradox (due to Smullyan):

In an non-empty room we can find someone with the following property:
if this person drinks, then everybody in the room drink.

Declare in Coq the needed elements to formalize the problem (cf. the previous exercise).

State and prove this paradox (thanks to excluded-middle).
*)
Parameter E : Type.      (* All the persons in the room *)
Parameter P : E -> Prop. (* Predicate telling if somebody drinks *)
Parameter e0 : E.        (* the name of a person in the room *)

Lemma notexistsnot : ~(exists e, ~P e) <-> forall e, P e.
Proof. 
  split.
  - intros. 
    apply not_not_elim. 
    intros npe.
    apply H.
    exists e.
    apply npe.

  - intros H.
    intros W.
    destruct W as (e, W).
    apply W.
    apply H.
Qed.

Lemma Drinker_paradox : exists e, P e -> (forall y, P y).
Proof.
  destruct (exm (exists e, ~P e)).
  - (* there is a non-drinker : it's our witness ! *)
  destruct H as (x,Hx).
  exists x. intros Hx'. destruct Hx. assumption.
  - (* there is not a non-drinker: everybody drinks thanks to notexistsnot *)
  exists e0. intro. apply notexistsnot. apply H.
Qed.

End Exercise2.  

Module Exericse3.
(** Exercice 3 : Subsets **)

(*
Given a type E:Type in Coq, we consider subsets of E, represented here as unary predicates on E, i.e. objects of type E->Prop.
*)
Parameter E : Type.
Definition sets := E -> Prop.

(*
Define in Coq the binary predicate subset : (E->Prop)->(E->Prop)->Prop expressing the inclusion of two subsets. Show that this relation is reflexive and transitive. Is is antisymmetric ?
*)
Definition subset (A B :sets):Prop :=
  forall x:E, A x -> B x.

Lemma subset_relf : forall A, subset A A.
Proof.
  unfold subset.
  intro A.
  intros.
  apply H.
Qed. 

Lemma subset_trans : forall A B C, subset A B /\ subset B C -> subset A C.
Proof.
  unfold subset.
  intros.
  destruct H as (HAB, HBC).
  apply HBC.
  apply HAB.
  apply H0.
Qed.

(*
Define in Coq a binary predicate eq : (E->Prop)->(E->Prop)->Prop expressing the extensional equality of two subsets. Show that it is indeed a equivalence relation. Show that subset is antisymmetric with respect of eq.
*)
Definition eq (A B: sets):Prop :=
  forall x, (A x <-> B x).

Lemma eq_refl : forall A, eq A A.
Proof.
  unfold eq.
  intro A.
  intro x.
  split; intro H; apply H.
Qed.

Lemma eq_trans : forall A B C, eq A B /\ eq B C -> eq A C.
Proof.
  unfold eq in *.
  intros A B C.
  intros (HAB, HBC).
  
  split; intros; [apply HBC; apply HAB | apply HAB; apply HBC]; assumption.
Qed.

Lemma eq_symm : forall A B, eq A B -> eq B A.
Proof. 
  unfold eq.
  intros A B H.
  split; apply H. 
 Qed.

(* Show that subset is antisymmetric with respect of eq. *)
Lemma subset_antisym_eq : forall A B, (subset A B /\ subset B A) -> eq A B.
Proof.
  intros A B (SAB, SBA).
  unfold subset in *.
  unfold eq.
  intro x.
  split.
  - apply SAB.
  - apply SBA.
Qed.
   
  
(* Define in Coq the "union" and "intersection" operators on subsets of E. Show that theses operations are associative, commutative, idempotent and distributive (one on the other).
*)

Definition union (A B: sets) : sets := fun x => A x \/ B x.
Definition inter (A B: sets): sets := fun x => A x /\ B x.

Lemma union_assoc : forall A B C, eq (union (union A B) C) (union A (union B C)).
Proof.
  intros A B C.
  unfold eq.
  unfold union.
  intros.
  split.
  - intros H. 
    destruct H as [[ax | bx ]| cx ]; [left | right; left | right; right]; assumption.
  - intros H.
    destruct H as [ ax | [bx|cx]]; [left; left | left; right | right]; assumption.
Qed.

Lemma union_comm' : forall A B, eq (union A B) (union B A).
Proof.
  intros A B.
  unfold eq, union.
  firstorder.
Qed.

Lemma union_comm : forall A B, eq (union A B) (union B A).
Proof.
  intros A B.
  unfold eq, union.
  intros x. split.
  - intros; destruct H as [ax | bx]; [right | left]; assumption.
  - intros; destruct H as [bx | ax]; [right | left]; assumption.
Qed.

Lemma union_idempotent : forall A, eq (union A A) A.
Proof.
  unfold eq, union.
  intros A x.
  split.
  - intro H. destruct H as [a|b]; assumption.
  - intro ax. left. assumption.
Qed.

Lemma inter_assoc : forall A B C, eq (inter (inter A B) C) (inter A (inter B C)).
Proof.
  intros A B C.
  unfold eq.
  unfold inter.
  intros.
  split.
  - intros H. 
    destruct H as ((ax , bx ), cx ); repeat split; assumption.
  - intros H.
    destruct H as (ax , (bx , cx )); repeat split; assumption.
Qed.

Lemma inter_comm : forall A B, eq (inter A B) (inter B A).
Proof.
  intros A B.
  unfold eq, inter.
  intros x. split.
  - intros; destruct H as (ax , bx); split; repeat assumption.
  - intros; destruct H as (bx , ax); split; repeat assumption.
Qed.

Lemma inter_idempotent : forall A, eq (inter A A) A.
Proof.
  unfold eq, inter.
  intros A x.
  split.
  - intro H. destruct H; assumption.
  - intro. split; assumption.
Qed.

Lemma distr_nu : forall A B C, eq (inter A (union B C)) (union (inter A B) (inter A C)) .
Proof.
  intros A B C.
  unfold eq, inter, union. 
  intros x.
  split.
  - intros (ax, [bx | cx]); [left | right]; split; repeat assumption.
  - intros [(ax, bx)|(ax, cx)]; split; [ | left | | right]; assumption.
Qed.

Lemma distr_un : forall A B C, eq (union A (inter B C)) (inter (union A B) (union A C)) .
Proof.
  intros A B C.
  unfold eq, inter, union. 
  intros x.
  split.
  - intros [ax | (bx , cx)]; split; [left| left| right| right]; assumption.  
  - intros ([ax| bx], [aax| cx]); [left|left|left|right]; try split; repeat assumption.
Qed.