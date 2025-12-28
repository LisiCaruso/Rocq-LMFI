(* We consider here data structures that are purely functional (also said persistent or immutable) and allow us to encode lists. We have already seen the Coq standard implementation of lists, but more generally a list is here a finite sequence of elements  where the order of elements 

in the list is meaningful and where the operations "on the left" are efficient, both a cons extension operation and a head and a tail access functions.
Actually, instead of two separated head and tail functions, we will consider here a unique function uncons doing both. More precisely, uncons l = Some (h,t) whenever the list has a head h and a tail t and uncons l = None whenever l is empty.


We will also focus on a "nth" function for our lists, allowing us to perform "random" access anywhere in a liste, not just on the left.
The goal of this work is to implement lists in various manners, ending with nth functions of logarithmic complexity without compromising too much the cost of functions cons and uncons (and ideally keeping this cost constant). Here, the complexity we consider is the number of access to any part of any innner substructure, in the worst case, expressed in function of the number of elements present in the list. In a first time, we neglect the cost of any arithmetical operations we may perform on integers. *) 

(** Exercise 1 : Implementation via regular Coq lists *)
Require Import List.
Import ListNotations.
Require Import Arith.

Module RegularList.
(* Implement the following operations on the Coq usual list datatype, and give their complexity. 

cons : forall {A}, A -> list A -> list A.
uncons : forall {A}, list A -> option (A * list A).
nth : forall {A}, list A -> nat -> option A.
*)

Definition cons {A} (x: A) (l : list A) : list A := x::l.

Definition uncons {A} (l: list A) : option (A * (list A)) :=
  match l with 
  | [] => None
  | x::l' => Some (x, l')
end. 

Fixpoint nth {A} (l : list A) (n : nat): option A := 
let l_un:= uncons l in
  match n with 
  | 0   => match l_un with 
           | None => None
           | Some (a, l') => Some a
          end
  | S n' => match l_un with 
            | None => None
            | Some (a, l') => nth l' n'
          end
end. 

Compute nth [1;2;3] 1.
Compute nth [1;2;3] 0.
Compute nth [1;2;3] 10.

End RegularList.

(** Exercise 2 : Implementation via b-lists (a.k.a binary lists) *)
Module BList.

(* Define a Coq type blist : Type -> Type corresponding to b-list, i.e. list of binary trees with data at the leaves. 

No need to enforce in blist the other constraints (trees that are all perfect and are of strictly increasing sizes). But you should always maintain these invariants when programming with blist. And if you wish you may write later boolean tests checking whether a particular blist fulfills these invariants. *)

(** define type of trees
blist is the type of a list of trees *)

Inductive tree' A :=
| Leaf' (a :A) :  tree' A
| Node' (a b: tree' A): tree' A.

Inductive btree A :=
| Leaf : A -> btree A
| Node : btree A -> btree A -> btree A.

Definition blist A := list (btree A* nat). 

Arguments Leaf {A}.
Arguments Node {A}.

Definition example : blist nat:= [(Leaf 2, 0) ; (Node (Leaf 2) (Leaf 2), 1)].
Check example.

(* (Optional) Adjust your blist definition in such a way that retrieving the sizes (or depth) of a tree inside a blist could be done without revisiting the whole tree. *)

(* On this blist type, implement operations cons, uncons and nth. Check that all these operations are logarithmic (if you did the last suggested step). *)

Fixpoint depth {A} (t : btree A) : nat :=
  match t with 
  | Leaf _ => 0
  | Node a b => S (max (depth a) (depth b))
end.

(* cons *)

Fixpoint aux {A} (t: btree A) (n: nat) (l: blist A): blist A :=
match l with 
  | [] => [(t, depth t)]
  | (a, m)::l' => if  n <? m then (t, n)::l
                  else aux (Node t a) (S n) l'
end. 

Definition cons {A} (t: btree A) (l: blist A): blist A := aux t (depth t) l.
Definition cons_leaf {A} (a: A) (l: blist A) : blist A := cons (Leaf a) l.

Definition uncons {A} (l: blist A) : option (btree A * (blist A)) :=
  match l with 
  | [] => None
  | (x, n)::l' => Some (x, l')
end. 

Fixpoint nth_btree {A} (t : btree A) (n : nat): option A := 
  match t with 
  | Leaf a => if n =? 0 then Some a else None
  | Node t1 t2 => let size_t1 := 2^(depth t1) in 
                  if n <? size_t1 then nth_btree t1 n
                  else nth_btree t2 (n-size_t1)
end. 

Fixpoint nth_blist {A} (bl: blist A) n : option A :=
 match bl with
 | [] => None
 | (t, k)::bl' =>
   let size_t := 2^depth t in
   if n <? size_t then nth_btree t n
   else nth_blist bl' (n -  size_t)
 end.

(* digression : from regular list to blist and back *)
Fixpoint list_to_blist {A} (l:list A) : blist A :=
 match l with
 | [] => []
 | x::l => cons_leaf x (list_to_blist l) 
 end.

Definition aa := list_to_blist [1;2;3;4;5;6;7].


Fixpoint btree_to_list {A} (t: btree A) : list A :=
 match t with
 | Leaf a => [a]
 | Node t t' => btree_to_list t ++ btree_to_list t'
 end.

Compute nth_blist (list_to_blist [1;2;3;4;5;6;7]) 7.
Compute list_to_blist [1;2;3;4;5;6;7].
(* end of digression *)

Check Nat.log2.
Compute (2^4).
Compute Nat.log2 16.




(* On this blist type, implement operations cons, uncons and nth. Check that all these operations are logarithmic (if you did the last suggested step).


Finish the current module : End BList.


This b-list structure shows that a fast random access in a list-like structure is indeed possible. But this comes here at an extra cost : the operations "on the left" (cons and uncons) have a complexity that is not constant anymore. We'll see now how to get the best of the two worlds. But first, some arithmetical interlude : in the same way the b-lists were closely related with the binary decomposition of number, here comes an alternative decomposition that may help us in exercise 4.

*)

End BList.

(** EXERCISE 3**)
(* Exercise 3 : Skew binary number system
We call skew binary decomposition (or sb-decomposition) of a number its decomposition as sum of numbers of the form 2^k -1 with k>0. Moreover all the terms in this sum must be differents, except possibly the two smallest ones.


Write a decomp function computing a sb-decomposition for any natural number. Could we have different ordered sb-decompositions of the same number ?
*) 
Fixpoint decomp (n : nat): list nat := 
  n


(*Write two functions next and pred that both take the sb-decomposition of a number, and compute the sb-decomposition of its successor (resp. precedessor), without trying to convert back the number in a more standard representation, and moreover without using any recursivity (no Fixpoint) apart from a possible use of Nat.eqb.


For the last section, we admit that the sb-decomposition of a number n is a sum whose number of terms is logarithmic in n.*)
