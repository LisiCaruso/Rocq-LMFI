Require Export ZArith.
Require Export String.
Require Export List.

Open Scope Z_scope.

Inductive aexpr: Type := 
 Avar : string -> aexpr
|Anum : Z -> aexpr
|Aplus : aexpr -> aexpr -> aexpr
|Aminus : aexpr -> aexpr -> aexpr
|Amul : aexpr -> aexpr -> aexpr
.

Inductive bexpr: Type :=
  Blt : aexpr -> aexpr -> bexpr
| Beq : aexpr -> aexpr -> bexpr.

Inductive instr: Type :=
 Assign : string -> aexpr -> instr
|Seq : instr -> instr -> instr
|While : bexpr -> instr -> instr
|Skip : instr
.

Definition env := list(string*Z).

Inductive aeval : env -> aexpr -> Z -> Prop :=
 Aeint : forall e n, aeval e (Anum n) n
|Ae_var1 : forall e x n, aeval ((x,n)::e) (Avar x) n
|Ae_var2 : forall e x y v v', x<>y -> aeval e (Avar x) v -> 
                                      aeval ((y,v')::e) (Avar x) v
|Ae_plus : forall e e1 e2 v1 v2, aeval e e1 v1 ->
                                 aeval e e2 v2 ->
                                 aeval e (Aplus e1 e2) (v1 + v2)
|Ae_minus : forall e e1 e2 v1 v2, aeval e e1 v1 ->
                                 aeval e e2 v2 ->
                                 aeval e (Aminus e1 e2) (v1 - v2)
|Ae_mul : forall e e1 e2 v1 v2, aeval e e1 v1 ->
                                 aeval e e2 v2 ->
                                 aeval e (Amul e1 e2) (v1 * v2)
.


Inductive beval : env -> bexpr -> bool -> Prop :=
 Be_lt1 : forall e e1 e2 v1 v2, aeval e e1 v1 ->
                                aeval e e2 v2 ->
                                v1 < v2 ->
                                beval e (Blt e1 e2) true
|Be_lt2 : forall e e1 e2 v1 v2, aeval e e1 v1 ->
                                aeval e e2 v2 ->
                                v1 >= v2 ->
                                beval e (Blt e1 e2) false
.

Lemma det_aeval : forall E a v1 v2,
  aeval E a v1 -> aeval E a v2 -> v1=v2.
Proof.
Admitted.

Lemma det_beval : forall E a v1 v2,
  beval E a v1 -> beval E a v2 -> v1=v2.
Proof.
Admitted.

Inductive e_update : env->string->Z->env->Prop :=
| s_up1 : forall r x v v', e_update ((x,v)::r) x v' ((x,v')::r)
| s_up2 : forall r r' x y v v', e_update r x v' r' ->
            x <> y -> e_update ((y,v)::r) x v' ((y,v)::r').

Parameter incr_init_var : env -> string -> env -> Prop.

Inductive exec : env->instr->env->Prop :=
| SN_Skip : forall E, exec E Skip E
| SN_Assign : forall E E' x e v, aeval E e v -> e_update E x v E' ->
                           exec E (Assign x e) E'
| SN_Seq : forall E E' E'' i1 i2,
    exec E i1 E' -> exec E' i2 E'' -> exec E (Seq i1 i2) E''
| SN_While_1 : forall E E' E'' b i,
    beval E b true -> exec E i E' -> exec E' (While b i) E'' -> 
                      exec E (While b i) E''
| SN_While_2 : forall E b i,
    beval E b false -> exec E (While b i) E
.

Open Scope string_scope.

Parameter init : env -> string -> env -> Prop.

Definition incr (v:string):= Assign v (Aplus (Avar v) (Anum 1)).

Lemma test: exec (("x",1):: nil) (incr "x") (("x",2):: nil).
Proof.
(* to be completed *)
Admitted.



Inductive sos_step : env->instr->instr->env->Prop :=
  SOS_Assign : forall E E' x e v,
   aeval E e v -> e_update E x v E' ->
   sos_step E (Assign x e) Skip E'
| SOS_Skip : forall E i, sos_step E (Seq Skip i) i E
| SOS_Seq : forall E E' i1 i1' i2,
               sos_step E i1 i1' E' ->
               sos_step E (Seq i1 i2)(Seq i1' i2) E'
| SOS_While1 :
     forall E b i, beval E b true ->
       sos_step E (While b i) (Seq i (While b i)) E
| SOS_While2 :
     forall E b i, beval E b false ->
       sos_step E (While b i) Skip E
.

Hint Resolve SOS_Assign SOS_Skip SOS_Seq SOS_While1 SOS_While2.


Inductive sos_star : env->instr->instr->env->Prop :=
  SOS_zero_step : forall E i, sos_star E i i E
| SOS_step_star : forall E E' E'' i i' i'',
             sos_step E i i' E' -> sos_star E' i' i'' E'' ->
             sos_star E i i'' E''.

Hint Resolve SOS_zero_step SOS_step_star.

Lemma sos_star_trans :
   forall r r' r'' i i' i'',
    sos_star r i i' r' -> sos_star r' i' i'' r'' ->
    sos_star r i i'' r''.
Proof.
Admitted.

Lemma sos_sequence_aux : forall r i is r',
  sos_star r i is r' -> is = Skip ->
  forall i' i'' r'', sos_star r' i' i'' r'' ->
  sos_star r (Seq i i') i'' r''.
Proof.
Admitted.

Lemma sos_sequence : forall E E' E'' i i',
  sos_star E i Skip E' -> sos_star E' i' Skip E'' ->
  sos_star E (Seq i i') Skip E''.
Proof.
intros.
eapply sos_sequence_aux;eauto.
Qed.


Lemma sn_imp_sos :
 forall E E' i, exec E i E' -> sos_star E i Skip E'.
Proof.
 (* to be completed *)
Admitted.


Inductive assert : Type :=
  a_b : bexpr -> assert 
| a_not: assert -> assert 
| a_conj:  assert -> assert -> assert
| a_imp : assert -> assert -> assert.
 

Fixpoint af (g:string->Z)(a:aexpr) {struct a} : Z :=
  match a with
    Avar s => g s
  | Anum n => n
  | Aplus e1 e2 => af g e1 + af g e2
  | Aminus e1 e2 => af g e1 - af g e2 
  | Amul e1 e2 => af g e1 * af g e2
  end.

Definition bf (g:string->Z)(b:bexpr) : Prop :=
 match b with
   Blt e1 e2 => af g e1 < af g e2
 | Beq e1 e2 => af g e1 = af g e2
 end.

Fixpoint i_a  (g:string->Z)(a:assert) {struct a}: Prop :=
  match a with
    a_b e => bf g e
  | a_not a => ~ i_a  g a
  | a_conj a1 a2 => i_a g a1 /\ i_a g a2
  | a_imp a1 a2 => i_a g a1 -> i_a g a2
  end.


Definition valid  (a:assert) :=
  forall (g:string->Z), i_a g a.

(* First define substitution operations and then Hoare's logic:*)

Inductive ax_sem : assert -> instr -> assert -> Prop :=
  HoareSkip : forall P, ax_sem P Skip P
 (* To be completed *)
.

(* Show that {x > 0} x := x + 1 {x > 0} 
 To be completed.
*)

(* Show that {x > 0} x := x + 2; x := x − 1 {x > 0} 
 To be completed.
*)

(*
 Define the program: 
1x:=3; if x < 4 then x:=x+1 else (x:=x+1;x:=x+1)
*)

(* Show that in any environment defining x, the execution of the previous program
produces an environment where x is equal to 4. *)

(* 
Define the program :
x:=3; while x < 5 do x:=x+1 done
*)

(*
 Show that in any environment defining x, the execution of the previous program
produces an environment where x is equal to 4.
*)





