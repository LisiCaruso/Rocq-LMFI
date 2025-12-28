Check 1=1.

Definition id_1 : forall X, X->X := fun (X:Type)(x:X) => x.
(*Eserizio 1 esercitazione 1*) 

Definition compose1 : forall A B C : Type, (B->C)->((A->B)->(A->C)) (*questo è il tipo del risultato*) := 
fun (A B C : Type) (bc : B->C) (ab : A->B) (a : A) =>  bc(ab(a)). 


Definition compose2 : forall A B C : Type, (B->C)->((A->B)->(A->C)) (*questo è il tipo del risultato*) := 
fun (A B C : Type) (bc : B->C) (ab : A->B)  => fun a =>  bc(ab(a)). 

(*I want to produce an elemente from c from B, C, A and *)

Check S 3 = 4.

Compute (compose2 nat nat nat S S 3).
Print compose2 (nat nat nat S S 3).
Check (compose2 nat nat nat).

Compute (compose2 nat nat nat).

(*AMINE HELP*)

Definition compose : forall A B C : Type, (B->C)->(A->B)->(A->C) :=
  fun (A B C : Type) a b c => a (b c).

Definition compose' : forall A B C : Type, (B->C)->(A->B)->(A->C) :=
  fun (A B C : Type) a b => fun x => a (b x).

Definition compose'' : forall A B C : Type, (B->C)->(A->B)->(A->C) :=
  fun (A B C : Type) a => fun y => fun x => a (y x).

Definition compose''' : forall A B C : Type, (B->C)->(A->B)->(A->C) :=
  fun (A B C : Type) => fun z => fun y => fun x => z (y x).

Definition compose'''' : forall A B C : Type, (B->C)->(A->B)->(A->C).
Proof.
  intros A B C.
  intros BC AB.
  intros a.
  exact (BC (AB a)).
Qed.

Definition compose''''' : forall A B C : Type, (B->C)->(A->B)->(A->C).
Proof.
  intros A B C.
  intros BC AB.

  exact (fun a => (BC (AB a))).  (*we can also make a a function*)
Defined. (*This proof corresponds to the program we print afterwards*)

Print compose'''''.




