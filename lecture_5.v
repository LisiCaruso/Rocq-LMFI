(** * Session 5 : dependent types (again), monads, modules *)

(** M2 LMFI *)

Require Import List Arith.
Import ListNotations.

(** * Part I : Some more about dependent types *)

(** Ia) : Perfect binary trees, this time via inductive types.
    Just as vectors compared to lists, we add an extra argument in nat,
    here encoding the depth of the tree.
*)

Inductive fulltree (A:Type) : nat -> Type :=
| FLeaf : A -> fulltree A 0
| FNode n : fulltree A n -> fulltree A n -> fulltree A (S n).

Arguments FLeaf {A}.
Arguments FNode {A} {n}.

Check FNode (FNode (FLeaf 1) (FLeaf 2)) (FNode (FLeaf 1) (FLeaf 2)).


(** Ib) Dependent pairs (also known as dependent sums). *)

(** We have seen that the arrow type [A->B] has a dependent counterpart,
    the product [forall x:A, B x] (also called Π-type).
    For the pair type [A*B], its dependent version is called
    sigT (for Σ-type), with a notation [{x:A & B x}]. *)

Print sigT. (* the inductive type, with syntax { ... & ... } *)
    (* Inductive sigT (A : Type) (P : A -> Type) : Type :=
        existT : forall x : A, P x -> {x : A & P x}.

    Arguments sigT [A]%type_scope P%type_scope
    Arguments existT [A]%type_scope P%function_scope x _
    *)
Check existT. (* its constructor *)
(* Inductive sigT (A : Type) (P : A -> Type) : Type :=
    existT : forall x : A, P x -> {x : A & P x}.

Arguments sigT [A]%type_scope P%type_scope
Arguments existT [A]%type_scope P%function_scope x _ 
*)

(** Just as the conclusion of a product may have a type [B x] which
    depends on the value [x] of the input, here the right component
    of this pair [{x:A & B x}] will have a type [B x] which depends
    on the value [x] present on the left of this pair.
    As the name [existT] of the constructor may suggests, this type
    can also be seen as an existential type : "there exists an x in
    A such that the right component is in [B x]". *)

(** Example : a type of all perfect binary trees on a domain A,
    regardless of theirs depth *)

Definition all_fulltrees A := { n : nat & fulltree A n }.
(* reads as "there exists n such that n is natural and A is a fulltree of size n" *) 

Definition some_fulltree : all_fulltrees nat :=
  existT _ 1 (FNode (FLeaf 1) (FLeaf 2)).

Definition some_fulltree':=
  existT _ 1 (FNode (FLeaf 1) (FLeaf 2)).
Check some_fulltree.
Print some_fulltree.
Print some_fulltree'.
(* the _ is here the "predicate" B, that Coq can infer here as being
   [fulltree nat]. *)
(* 
        some_fulltree = 
        existT (fun n : nat => fulltree nat n) 1
          (FNode (FLeaf 1) (FLeaf 2))
             : all_fulltrees nat 

        some_fulltree' = 
       existT (fulltree nat) 1 (FNode (FLeaf 1) (FLeaf 2))
            : {x : nat & fulltree nat x}

*)

(** Actually, Coq could even guess here the second argument ([1]),
    by typing the last one (obtaining [fulltree A 1] here). *)

Definition some_fulltree'':=
  existT _ _ (FNode (FLeaf 1) (FLeaf 2)).

Check existT _ _ (FNode (FLeaf 1) (FLeaf 2)).

(** Some predefined projections *)

Compute projT1 some_fulltree.
Compute projT2 some_fulltree.
 (* of type : (fun n : nat => fulltree nat n) (projT1 some_fulltree)
    which is convertible to : fulltree nat 1 *)
Check projT1.
(* 
  projT1
     : forall (A : Type) (P : A -> Type),
       {x : A & P x} -> A
*)
Check projT2.
(* 
  projT2
     : forall (A : Type) (P : A -> Type)
         (x : {x : A & P x}), P (projT1 x)
*)

(** See TD5 : we could redo the start of TD4, this time ensuring
   *by typing* that all the trees we manipulate are perfect : *)

Definition blist (A:Type) := list { n & fulltree A n }.

(** For instance : *)

Definition singleton {A} (a:A) : blist A := [ existT _ 0 (FLeaf a) ].
Print singleton.

(** We will see later a few other existential types :
    - the type of existential statements [exists x:A, B x]
      where A and B are in universe Prop.
    - the "mixed" existential type [{x:A | B x}] (with underlying
      type name [sig]), where B is a logical statement in Prop,
      but A is in Type (we call A an "informative" or "relevent" type).
*)


(** Ic) Fin *)

(** Another famous dependent type : type [Fin n], encoding a canonical
    finite set with exactly [n] elements. Or said otherwise, the type
    of all numbers strictly less than [n]. So this type is also called
    the "bounded integers". *)

Inductive Fin : nat -> Type :=
 | Zero n : Fin (S n)
 | Succ n : Fin n -> Fin (S n).

(* As usual, let's get rid of some "boring" arguments *)
Arguments Zero {n}.
Arguments Succ {n}.

(** Nobody can be in type [Fin 0], since all constructors of [Fin]
   have final types of the form [Fin (S ...)]. *)
  
(** Then [Fin 1] is a type with just one element *)

Check (Zero : Fin 1).
Fail Check (Succ Zero : Fin 1).
Check (Succ Zero : Fin 2).

(** Then [Fin 2] is a type with two elements, but no more *)

Check (Zero : Fin 2).
Check (Succ Zero : Fin 2).
Fail Check (Succ (Succ Zero) : Fin 2).

(* If we convert inhabitants of [Fin n] back to [nat] by forgetting
   all the inner implicit arguments, then we indeed get all [nat]
   numbers strictly less than [n]. *)

Fixpoint fin2nat {n} (m : Fin n) : nat :=
 match m with
 | Zero => 0
 | Succ m' => S (fin2nat m')
 end.

Compute fin2nat (Succ (Succ Zero): Fin 3).

Definition all_fin3 : list (Fin 3) := [Zero; Succ Zero; Succ (Succ Zero)].
Compute List.map fin2nat all_fin3.

(** Note : another approach for defining such "bounded" integers is to
   use an existential type to restrict nat. *)

Definition bounded_nat n := { p:nat | p < n }.
Compute bounded_nat 4.
(*      = {x : nat | S x <= 4}
     : Set
*)
Definition bounded_eq_nat n := { p: nat | p <= n}.
Compute bounded_eq_nat 4.
(* 
     = {x : nat | x <= 4}
     : Set
*)

(** Pros : easy projection to nat, no need for a reconstruction like
    [fin2nat] above.
    Cons : This implies to work with logical predicate [ < ] (in Prop,
    not the boolean comparison we're been using up to now) and
    build arithmetical proofs. This is hence less suitable for the
    [Vnth] function below (no nice inductive structure). *)


(** Id) Application: [Vnth]

    The type [Fin] of "bounded" integers provides a neat way to
    specify and implement a safe access to the n-th element of
    a vector (type [vect] seen last week). *)

Inductive vect (A:Type) : nat -> Type :=
 | Vnil : vect A 0
 | Vcons n : A -> vect A n -> vect A (S n).

Arguments Vnil {A}.
Arguments Vcons {A} {n}.
Definition a2 :=  (Vcons 0 (Vcons 2 (Vcons 3 Vnil))).
(** For a vector v in type [vect A n], we can access any position
    [p] as long as [p] is in [Fin n] (hence garanteed to represent
    a number strictly less than [n]. *)

Fixpoint Vnth {A} {n} (p:Fin n) : vect A n -> A :=
 match p with
 | Zero => fun v => match v with Vcons x _ => x end
 | Succ p' => fun v => Vnth p' (match v with Vcons _ v => v end)
 end.

Compute Vnth (Succ (Succ Zero)) a2.
  (*
   Inductive Fin : nat -> Type :=
   | Zero n : Fin (S n)
   | Succ n : Fin n -> Fin (S n).
*)
(** Note : this type of programming is still relatively new in Coq,
    and still very fragile. For instance, in the previous
    example, one may be tempted to move the recursive call [Vnth]
    inside the final [match v], and hence write:

     | Succ p => fun v => match v with Vcons _ v => Vnth p v end

    But this is rejected by Coq for the moment. Similarly, no way
    (yet ?) to move out the two [fun v =>] and factorize them in one
    [fun v =>] outside of [match p]. *)

(** Example of use: with a vector of size 3, one may access to elements
    at position 0, 1, 2 but not 3. *)

Definition testvec := Vcons 1 (Vcons 2 (Vcons 3 Vnil)).
Compute testvec.
(*      = Vcons 1 (Vcons 2 (Vcons 3 Vnil))
     : vect nat 3
 è il vettore (1, 2, 3)
*)
Compute Vnth Zero testvec.
Compute Vnth (Succ Zero) testvec.
Compute Vnth (Succ (Succ Zero)) testvec.
Fail Compute Vnth (Succ (Succ (Succ Zero))) testvec.



(** * Part II : Monads *)

(** IIa) Introduction to monads, a.k.a. surviving the "option" type *)

(** Let's consider again the access fonctions on Coq lists,
    written with [option] : *)

Definition head {A} (l:list A) : option A :=
 match l with
 | [] => None
 | x :: _ => Some x
 end.

Definition tail {A} (l:list A) : option (list A) :=
 match l with
 | [] => None
 | _ :: l => Some l
 end.

(** Running example : let's sum the two first elements of a list.
    Of course, we could do that directly. *)

Definition sumtwofirst l :=
 match l with
 | a::b::_ => Some (a+b)
 | _ => None
 end.

(** But if we want now to do that with the previous [head] and [tail]
    functions, that's quite cumbersome, due to lots of nested [match] *)

Definition sumtwofirst_v2 l :=
 match head l with
 | None => None
 | Some a =>
   match tail l with
   | None => None
   | Some l' =>
     match head l' with
     | Some b => Some (a+b)
     | _ => None
     end
   end
 end.

(** Some abstraction, via an higher-order function *)

(** 1st attempt, let's try to convert a option to another option,
    and use this function instead of all nested [match]. *)

Definition option_map {A B} (o : option A)(f:A -> B) : option B :=
 match o with
 | Some x => Some (f x)
 | None => None
 end.

Definition sumtwofirst_v3 l :=
 option_map (head l)
   (fun a => option_map (tail l)
      (fun l' => option_map (head l')
         (fun b => a+b))).

Check sumtwofirst_v3. (* But that's not the right type !! *)

(** Better: a kind of "composition" of options *)

Definition option_bind {A B} (o : option A) (f:A -> option B) : option B :=
 match o with
 | Some x => f x
 | None => None
 end.

Definition sumtwofirst_v4 l :=
 option_bind (head l)
   (fun a => option_bind (tail l)
      (fun l' => option_bind (head l')
         (fun b => Some (a+b)))).

Check sumtwofirst_v4. (* Ok this time *)

(** Same, with now a nice notation *)

Infix ">>=" := option_bind (at level 20, left associativity).

Definition sumtwofirst_v5 l :=
 head l >>= fun a =>
 tail l >>= fun l' =>
 head l' >>= fun b =>
 Some (a+b).

(** To be read as : "get the head of l, name it a if it succeed,
    then get the tail of l, name it l' if it succeed,
    then get the head of l', name it b if it succeed,
    then return (a+b) if everything worked." *)

Compute sumtwofirst_v5 [1;2;3].
Compute sumtwofirst_v5 [1].


(** IIb) The general case of monads *)

(** This option_bind is actually a particular case of a more general
    idea, the monads, i.e. structures with a sort of composition
    (called "bind"), and a way to inject into these structures.

    https://en.wikipedia.org/wiki/Monad_(functional_programming)
*)

(** In Coq, we can describe such a structure via the following
    [Module Type]. A module type is an interface (a.k.a. signature)
    for some future modules, the modules being groups of definitions.
    More on modules next week.

    Here a monad will be anything with a parameterized type [t] and
    two operations [ret] and [bind] on this [t], with the following
    types: *)

Module Type MONAD.
  Parameter t : Type -> Type.
  Parameter bind : forall {A B}, t A -> (A -> t B) -> t B.
  Parameter ret : forall {A}, A -> t A. (* ret, since return is a Coq keyword *)
End MONAD.

(** To be complete, a monad normally imposes the following rules
    (called monadic laws), with >>= being [bind]. Here we'll keep
    these laws implicit (i.e. not specify them in the module type).

return a >>= f   =  f a
m >>= return     =  m
(m >>= f) >>= g  =  m >>= (fun x -> (f x >>= g))

*)

(** IIc) The error monad : just some abstraction of the option type. *)

Module MErr <: MONAD. (* The module MErr will fulfill the signature MONAD. *)
  Definition t := option.
  Definition ret {A} := @Some A.
  Definition bind {A B} := @option_bind A B.
End MErr.

Infix ">>=" := MErr.bind (at level 20, left associativity).

Definition sumtwofirst_v6 l :=
 head l >>= fun a =>
 tail l >>= fun l' =>
 head l' >>= fun b =>
 MErr.ret (a+b).

(** Another example : multiply all leaves of a tree, and stop if you
    encounter a zero. *)

Inductive tree (A:Type) :=
| Leaf : A -> tree A
| Node : tree A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node {A}.

Fixpoint leafmul t :=
  match t with
  | Leaf n => if n =? 0 then None else MErr.ret n
  | Node g d =>
    leafmul g >>= fun mulg =>
    leafmul d >>= fun muld =>
    MErr.ret (mulg * muld)
  end.

(** Note that the [None] in the [Leaf] case is not a monadic operation.
    That's ok, monads are just a "common language", but each specific
    monad will have extra operations, both for building elements in
    the type [t A] as this [None], but even more important, to do
    something interesting with a [t A]. Otherwise with just [return]
    and [bind], this type [t] is a black hole, nothing gets out !
    Here with the error monad, we will want someday to check whether
    a [t A] (i.e. a [option A] is an error or a success. *)


(** IId) List monads *)

(** The idea behind the error monad was to have either one correct
    result, or zero in the case of an error during the computation.
    With a list monad, we push this idea further : a list monad can
    represent any number of correct results. *)

Module MList <: MONAD.
  Definition t := list.
  Definition ret {A} (a:A) := [a].
  Definition bind {A B} (l:list A) (f:A->list B) := List.flat_map f l.
End MList.

Infix ">>=" := MList.bind (at level 20, left associativity).

(** Example, cartesian product *)

Definition cartprod {A} {B} (l:list A)(l' : list B) :=
  l >>= fun a =>
  l' >>= fun b =>
  MList.ret (a,b).

(** To be read as : "pick any element in l, name it a,
    then pick any element in l', name it b,
    then return the pairs (a,b) in all these combinations". *)

Compute cartprod [1;2;3] [4;5].

(** An extra operation which is quite relevant for list monad :
    filtering. With it, we can select just specific elements in
    a list. *)

Definition filter {A} (f : A -> bool) : list A -> list A :=
 List.filter f.


(** IIe) State monad

      More complex, it allows to mimic the behavior of a memory that
      you can read and write. Since we are here in a purely functional
      world, without "in place" modification like in imperative
      programming, we simulate that through a function receiving
      the previous memory state, and returning the next memory state,
      alongside the produced result. Below, this memory state is
      just a number in [nat], otherwise with a polymorphic state
      we would not fulfill the [MONAD] interface. *)

Module MState <: MONAD.
  Definition t A := nat -> nat*A.
  Definition ret {A} (a:A) := fun (st:nat) => (st,a).
  Definition bind {A B} (m:t A) (f:A->t B) : t B :=
   fun st => let (st',a) := m st in f a st'.
End MState.

Infix ">>=" := MState.bind (at level 20, left associativity).

(** Here, [ret] just keep the state intact, and [bind] makes the
    state evolve through [m] in a intermediate state [st'], then
    [f a st'] goes from this intermediate state to a final state
    combined with a final result in type [B]. *)

(** Simulate a program that adds one in our memory *)

Definition read : MState.t nat :=
 fun (n:nat) => (n,n).

Definition write (n:nat) : MState.t unit :=
 fun _ => (n,tt).

Definition increment_memory : MState.t unit :=
  read >>= fun n => write (n+1).

(** For a more interesting example of use, see TD5 *)

