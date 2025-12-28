  (** Encode in Coq the Church numerals, for which the number n is represented by λfλx.(f (f (... (f x)))) where f is applied n times.
More precisely, define (without using nat nor any other inductive type):

 - a type church : Type

 - two constant zero and one of type church

 - a function succ of type church->church

 - two functions plus and mult of type church->church->church

 - a function power

 - a test iszero

 - Also define two functions 
 - - nat2church : nat -> church 
 - - church2nat : church -> nat *)

(* *)

(** Let us first analyze the type of Church numerals:
the statement of the exercise tells us that church is 
a function of two arguments, [f] and [x], which iterates 
[f] a certain number of time over [x]. 

Therefore [f] shall have a type of the form [X -> Y] 
and necessarily [X] must be the type of [x]. Moreover, 
since [f] can be iterated, the type of its codomain shall 
be the same as the type of its domain: [X]=[Y]. 
Moreover, we want this type to apply on any pair of arguments 
the first of which is iterable on the second, and we thus 
introduce a universal quantification (dependent product type)
ending up with [forall X, (X->X)->(X->X)] as a type of 
Church numerals.

*)
Definition church := forall X, (X->X)->(X->X).

(** in defining [zero, one, ...], it is not 
needed to give the type of each argument (and neither must 
we provide a name for the type argument [X]) 
when the type of the constant is given : *)

Definition zero : church := fun _ f x => x.
Definition one : church := fun church f x => f x.

(*
Definition one : church := fun _ f x => f x. è uguale a quello di prima! *)

(** in fact there is another candidates for one: *)

Definition onebis : church := fun _ f => f.
Definition two : church := fun _ f x => f (f x).

(** a function succ of type church->church*)
Definition succ : church -> church :=
 fun n => fun _ f x => n _ f (f x).

(** WHAT IS THE IMPLICIT PARAMETER UP HERE!!??!?!?!? ^^^*)
Check one.
Print one.
(*one = 
fun (church : Type) (f : church -> church) (x : church) => f x
     : church

Arguments one X _ _*)
Compute succ one. (*     
= fun (X : Type) (x : X -> X) (x0 : X) => x (x x0)
     : church
*)

Print zero.
(*zero = 
fun (X : Type) (_ : X -> X) (x : X) => x
     : church

Arguments zero X _ _*)
Compute succ zero. 
(*     = fun (X : Type) (x : X -> X) (x0 : X) => x x0
     : church
*)
Compute succ (succ zero).
(*      = fun (X : Type) (x : X -> X) (x0 : X) => x (x x0)
     : church
*)
(** scriviamo la funzione church2nat 
 - - church2nat : church -> nat *)

Definition church2nat : church->nat := fun ch => ch nat S 0.

Compute church2nat (succ one).

(** scriviamo la funzione nat2church
-- nat2church : nat -> church *)

Fixpoint nat2church (n:nat) :=
match n with 
| 0 => zero
| S m => succ (nat2church m)
end.
Compute nat2church 3.
Compute church2nat (nat2church 100).

(** In the following, we will use the ability of Coq 
to not require that we actually provide the actual 
type when it can be inferred to lighten the definitions.

But to be fully informative and in order to understand 
what happens with church_power, we provide below the 
definition of those functions providing explicitly the 
type instanciations: *)

(** scriviamo la somma 
-- church_plus : church -> church -> church *)
Definition church_plus (n m:church) : church :=
  fun _ f x => n _ f (m _ f x).

Check 2 = 2 : Prop.
Check church_plus one one. 
Compute church_plus zero zero.
Compute church_plus one two.
Compute church_plus one zero.
Compute church2nat (church_plus (nat2church 13) (nat2church 10)).

(** scriviamo il prodotto
-- church_mult : church -> church -> church *)
Definition church_mult  (n m: church) : church := 
  fun _ f => n _ (m _ f). 

(* Definition church_mult  (n m: church) : church := 
  fun _ f x=> n _ (m _ f) x. 

you can avoid writing x if it is the last both left and right
*)

Compute church_mult one two.
Compute church2nat (church_mult (nat2church 13) (nat2church 10)).

Definition church_pow (n m: church) : church := fun _ => m _ (n _ ).
Compute church_pow one two.

Compute church2nat (church_pow (nat2church 2) (nat2church 5)).

(** To compute whether n is equal to zero of not, we 
pass two arguments to n. The first one will be iterated 
n times on the second one. 
- Therefore, if n is zero, the first function is not 
iterated and the second argument is returned directly, 
this second argument should be [true]. 
- Otherwise, if n is not zero, the function will be 
iterated at least one and we would like is_zero n to 
return false, therefore it is sufficient that the 
first argument of n is the the constant function 
always returning zero, independently of its argument: 
[fun _ => false]. *)

Definition is_zero (n:church):bool := n _ ( fun _ => false) true. 

Compute is_zero(zero).
Compute is_zero(succ (one)).

(** Explicit typing of the above functions: *)

Definition church_plus_explicit (n m:church) : church :=
  fun X f x => n X f (m X f x).

Definition church_mult_explicit (n m:church) : church :=
 fun X f =>  n X (m X f).

Definition church_pow_explicit (n m:church) : church :=
 fun X =>  m (X->X) (n X).

Definition is_zero_explicit (n : church) : bool :=
  n bool (fun (b:bool) => false) true.


Definition church_pred (n:church) : church := 
  fun _ f x =>
    n _  (fun g h => h (g f)) (fun _ => x) (fun u => u).
















