(* Note: many proof scripts below are deliberately in a compact
   and "advanced" style, to highlight a few interesting features.
   It's not a problem if you solutions are longer, as long as Coq
   accepts them ! *)

Module Exercise1. (* This module avoids conflicts with parameters of exercise 2 *)

Parameters A B C : Prop.
Lemma E1F1 : A -> A.
Proof.
 intro.
 assumption.
Qed.

Lemma E1F2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
 (* Usual Coq style : backward reasoning, from goal C back to intermediate goal B then to A *)
 intros.
 apply H0.
 apply H.
 apply H1.
Qed.

Lemma E1F2bis : (A -> B) -> (B -> C) -> A -> C.
Proof.
 (* Forward reasoning is also possible, with different tactics : mix A->B with A to get B, etc *)
 intros.
 apply H in H1.
 apply H0 in H1.
 assumption.
Qed.

Print E1F2.
Print E1F2bis. (* almost the same, apart from a few "let" abbreviations *)

(* a more advanced script that the one in td1.md, using ";" to chain proofs
   and intros (...,...) to directly destruct the conjonctions. *)

Lemma E1F3 : A /\ B <-> B /\ A.
Proof.
 split; intros (?,?); split; assumption.
Qed.

Lemma E1F4 : A \/ B <-> B \/ A.
Proof.
 split.
 - intros [a|b].
   + right. assumption.
   + left. assumption.
 - intros [b|a].
   + right. assumption.
   + left. assumption.
Qed.

Lemma E1F4bis : A \/ B <-> B \/ A.
Proof.
 split.
 - intros [a|b]; [right|left]; assumption.
 - intros [b|a]; (right; assumption) || (left; assumption).
Qed.


Lemma E1F5 : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
 split.
 - intros ((a,b),c). repeat split; assumption.
 - intros (a,(b,c)). repeat split; assumption.
Qed.

Lemma E1F6 : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
 split.
 - intros [[a|b]|c].
   + left. assumption.
   + right; left. assumption.
   + right; right. assumption.
 - intros [a|[b|c]].
   + left; left. assumption.
   + left; right. assumption.
   + right. assumption.
Qed.

Lemma E1F7 : A -> ~~A.
Proof.
 intros a na. (* with two names to force breaking the negation notation *)

(* Other possibilities :
  unfold "~".
  unfold "~" in *  (* same, but also works on hypothesis *).
*)

 apply na.
 apply a.
Qed.

Lemma E1F7' : A -> ~~A.
Proof.
 intros.
 unfold "~" in *.
 intros.
 apply H0 in H. 
 apply H.
Qed.

Lemma E1F7'' : A -> ~~A.
Proof.
 intros.
 unfold "~" in *.
 intros.
 apply H0. 
 apply H.
Qed.


Lemma E1F8 : (A -> B) -> ~B -> ~A.
Proof.
 intros ab nb a.
 apply nb.
 apply ab.
 assumption.
Qed.

Lemma E1F9 : ~~(A \/ ~A).
Proof.
 intro.
 apply H. right.
 intro.
 apply H. left.
 assumption.
Qed.

End Exercise1.
Module Exercise2.

Parameter X Y : Set.
Parameter A B : X -> Prop.
Parameter R : X -> Y -> Prop.


Lemma E2F1' :
 (forall x, A x /\ B x) <->
  (forall x, A x) /\ (forall x, B x).
Proof.
  split.
  - split; intros x; destruct (H x); assumption.
  - intros; destruct H; split; [apply H |apply H0].
Qed.


Lemma E2F1 :
 (forall x, A x /\ B x) <->
  (forall x, A x) /\ (forall x, B x).
Proof.
 split.
 - split.
   + intros x.
     (* a bit of a hack, here apply H works !
        (special treatment of /\ by Coq *)
     (* more "regular" approach : break the conjunction in (H x) *)
     destruct (H x).
     assumption.
   + intros x. apply H.
 - intros (Ha,Hb) x. split.
   + apply Ha.
   + apply Hb.
Qed.

Lemma E2F2 :
 (exists x, A x \/ B x) <->
  (exists x, A x) \/ (exists x, B x).
Proof.
 split.
 - intros (x,[Ha|Hb]).
   + left. exists x. assumption.
   + right. exists x. assumption.
 - intros [(x,Ha)|(x,Hb)].
   + exists x. left. assumption.
   + exists x. right. assumption.
Qed.

Lemma E2F3 :
  (exists y, forall x, R x y) ->
    forall x, exists y, R x y.
Proof.
 intros H x.
 destruct H as (y,H).
 exists y.
 apply H.

(* or intros+break in one step :
 intros (y,H) x.
 exists y.
 apply H.
*)
Qed.

End Exercise2.

