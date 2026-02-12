
(** * A few words about the inversion tactics *)

(* Already seen : injection and discriminate :

   injection H  where H : S x = S y gives x = y
   injection H  where H : x::l = x'::l' gives both x=x' and l=l'
   discriminate H where H : O = S x conludes the goal
    (since this case is impossible)
*)

(* The tactic inversion is a generalization of both,
   trying to recover from an inductive predicate
   what situations may have lead to this concrete predicate.
*)

(** A mini toy formal system.

______
(0,0) Ax

(n,m)
_____
(n+1,m+1)  Rule S

*)

Inductive toy : nat -> nat -> Prop :=
   AxRule : toy 0 0
 | SRule : forall n m, toy n m -> toy (S n) (S m).

Lemma toy_3_3 : toy 3 3.
Proof.
apply SRule.
apply SRule.
apply SRule.
apply AxRule.
Qed.

(** To prove that something does not hold, we can find a property
 that holds for all provable statements, but not for the one we want to disprove.
 Here, for instance, in all provable statements, the two numbers are equal.
 So we can prove that toy 1 2 does not hold, since 1<>2
*)

Lemma toy_equal : forall n m, toy n m -> n = m.
Proof.
 intros n m H.
 induction H.
 reflexivity.
 rewrite IHtoy.
 reflexivity.
Qed.

Lemma not_toy_1_2: ~ toy 1 2.
Proof.
 intro H.
 assert (1=2).
  apply toy_equal with (n:=1)(m:=2).
  assumption.
 discriminate H0.
Qed.


Lemma my_not_toy_1_2: ~ toy 1 2.
Proof.
    intros H.
    assert (1=2).
    apply toy_equal with (n:=1)(m:=2).
    apply H.
    discriminate H0.
Qed. 

(* We can use inversion to prove that toy 1 2 is not provable, it corresponds
to an analysis of the rules which could have been used to derive it. *)

Lemma not_toy_1_2_inversion: ~ toy 1 2.
Proof.
intro.
inversion H.
inversion H2.
Qed.


Inductive even : nat -> Prop :=
 | even_O : even O
 | even_SS n : even n -> even (S (S n)).

Lemma even_2 : even 2.
Proof.
 apply even_SS.
 apply even_O.
Qed.

Lemma even_plus4 : forall n, even n -> even (4+n).
Proof.
 intros.
 simpl.
 apply even_SS.
 apply even_SS.
 assumption.
Qed.

(* Up to now, even_2 and even_plus4 are direct proofs,
   no need for inversion *)

Lemma not_even_one : ~even 1.
Proof.
 intro.
 (* Here, destruct H (or induction H) would forget that our number is 1 :-(
    Before destruct H, we need to save all details ourselves
    (for instance via "remember"). *)
 remember 1 as m.
 destruct H.
 - discriminate Heqm.
 - discriminate Heqm.
Qed.

(* inversion is here nicer than this remember + destruct,
   and way more general *)

Lemma not_even_one_bis : ~even 1.
Proof.
 intro.
 inversion H.
Qed.

Lemma even_plus3 n : even (3+n) -> even (1+n).
Proof.
 intro H.
 simpl in *.
 inversion H. (* subst. (* if you want to get rid of remaining equations *)*)
 assumption.
Qed.

(* Since equality is also an inductive predicate, inversion also works
   on equality hypothesis (and subsumes injection and discriminate). *)

Print eq.
Lemma test_inj x : S x = 0 -> False.
Proof.
intro H.
inversion H.
Qed.



(** * Impredicative encodings *)

(* Note that we can quantify on all propositions and get a new proposition.
   That's impredicativity. In Coq that's specific to Prop : the Type universe
   is predicative (i.e. not impredicative).
*)

Definition FalseBis : Prop := forall (P:Prop), P.

Lemma False_equiv : False <-> FalseBis.
Proof.
split. 
- intro. (* exfalso. apply H. *)
elim H.
- intro.
unfold FalseBis in *.
apply H.
Qed.

Definition TrueBis : Prop := forall (P:Prop), P -> P.

Lemma True_equiv : True <-> TrueBis.
Proof.
split.
- intro.
unfold TrueBis.
intro.
intro HP.
apply HP.
- intro.
exact I.
Qed.

(* Alternative disjunction *)

Definition OrBis (P Q : Prop) : Prop :=
 forall R:Prop, (P -> R) -> (Q -> R) -> R.

Lemma or_equiv P Q : P \/ Q <-> OrBis P Q.
Proof.
 split.
 - intro.
 destruct H.
 * unfold OrBis.
   intros.
   exact (H0 H).
 * unfold OrBis.
   intros.
   exact (H1 H).
- intros.
  unfold OrBis in *.
  apply H.
  intro HP.
  left.
  assumption.
  intro HQ.
  right.
  assumption.
Qed.

(* Alternative definition for exists *)

Definition ExistsBis {X}(P:X->Prop)
 := forall Q:Prop, (forall x, P x -> Q) -> Q.

Lemma Exists_equiv {X}(P:X->Prop) :
 (exists x, P x) <-> ExistsBis P.
Proof.
 split.
 - intro.
   destruct H.
   unfold ExistsBis.
   intros.
   exact (H0 x H).
- intros.
  unfold ExistsBis in *.
  apply H.
  intros.
  exists x.
  apply H0.
Qed.


(* Alternative conjunction *)

Definition AndBis (P Q : Prop) : Prop :=
 forall R:Prop, (P -> Q -> R) -> R.

Lemma and_equiv P Q : P /\ Q <-> AndBis P Q.
Proof.
 split.
- intro.
  unfold AndBis.
  intros.
  destruct H.
  apply H0.
  assumption.
  assumption.
- intros.
  unfold AndBis in *.
  apply H.
  intros.
  split.
  assumption.
  assumption.
Qed.

