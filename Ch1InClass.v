(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Ch1InClass

This file is a translation of Ch1InClass.thy as of 2015-01-15T16:27:06-05:00 (TODO: get the git version number or whatever)
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.

Section Ch1InClass.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section repeat_stuff.

Fixpoint repeat (f : nat -> nat) (n : nat) (x : nat) : nat :=
    match n with
    | 0    => x
    | S n' => repeat f n' (f x)
    end.
(* TODO: implement the notation similar to Isabelle's [("_^_ _" [90,90,90] 89)] *)


Theorem repeat_cycle :
    forall {f n x} m,
    repeat f n x = x -> repeat f (m * n) x = x.
Proof.
Abort.

End repeat_stuff.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section multirember_stuff.

(* these two hypotheses will be treated as assumptions within this section, but once we close the section they will become abstracted out as the first two arguments to everything defined here. The fact that equality on [A] is decidable is something we need to explicitly mention and pass around proof of, unlike in Isabelle. *)
Variable A : Type.
Hypothesis eq_A_dec : forall x y:A, {x = y} + {x <> y}.


Fixpoint multirember (a : A) (bs : list A) : list A :=
    match bs with
    | nil      => nil
    | b :: bs' =>
        match eq_A_dec a b with
        | left  _ => multirember a bs'
        | right _ => b :: multirember a bs'
        end
    end.


(* Much more straightforward than [multirember_not_member__sets] *)
Lemma multirember_not_member__lists : forall a bs, ~In a (multirember a bs).
Proof.
Abort.

(* Can't seem to find this in the libraries anywhere... *)
Fixpoint list_to_set (xs : list A) : set A :=
    match xs with
    | nil      => empty_set A
    | x :: xs' => set_add eq_A_dec x (list_to_set xs')
    end.

(* This version more closely matches the Isabelle version. *)
Lemma multirember_not_member__sets :
    forall a bs,
    ~set_In a (list_to_set (multirember a bs)).
Proof.
Abort.

End multirember_stuff.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section tree_stuff.

Inductive tree (A : Type) : Type :=
    | Leaf : tree A
    | Node : tree A -> A -> tree A -> tree A
    .

Fixpoint height {A} (T : tree A) : nat :=
    match T with
    | Leaf       => 0
    | Node L x R => 1 + max (height L) (height R)
    end.

Fixpoint leaves {A} (t : tree A) : nat :=
    match t with
    | Leaf       => 1
    | Node L x R => leaves L + leaves R
    end.

Theorem height_less_leaves : forall {A} (T : tree A), height T + 1 <= leaves T.
Proof.
Abort.


(* N.B., we could easily generalize this to work for any type [A] with a decidable equality. *)
Fixpoint keys (T : tree nat) : set nat :=
    match T with
    | Leaf       => empty_set nat
    | Node L x R =>
        set_union eq_nat_dec
            (keys L)
            (set_union eq_nat_dec
                (set_add eq_nat_dec x (empty_set nat))
                (keys R))
    end.


(* N.B., Isabelle's inductive sets are essentially Coq's indexed data types. That is, in Isabelle we have both a set ["BST"] and proofs that a given tree belongs to that set ["T \<in> BST"]. Analogously, in Coq we have the type of proofs that something is a binary search tree [BST T] and we can form the set of all trees which are binary search trees [{T : tree nat | BST T}]. The Isabelle version places more emphasis on the sets than the proofs; whereas, Coq places more emphasis on the proofs rather than the sets.

In terms of the Coq syntax, note that parametric arguments appear to the left of the colon (as shown above with the definition of [tree]) whereas indexed arguments appear to the right of the colon (as seen below). This looks subtle at first, but be sure not to get them mixed up. *)
Inductive BST : tree nat -> Set :=
    | bst_leaf : BST (Leaf nat)
    | bst_node :
        forall {L x R},
        (forall y, In y (keys L) -> y <= x) ->
        (forall z, In z (keys R) -> x <= z) ->
        BST L ->
        BST R ->
        BST (Node nat L x R)
    .

(* Can't seem to find this in the libraries, but I'm sure it's there somewhere. *)
(* cf., [Coq.Arith.Lt.le_or_lt] *)
Fixpoint le_dec m n : {m <= n} + {n < m} :=
    match m, n with
    | 0   , 0    => left  _ (le_n 0)
    | 0   , S n' => left  _ (le_0_n (S n'))
    | S m', 0    => right _ (lt_0_Sn m')
    | S m', S n' =>
        match le_dec m' n' with
        | left  m'_le_n' => left  _ (le_n_S m' n' m'_le_n')
        | right n'_lt_m' => right _ (lt_n_S n' m' n'_lt_m')
        end
    end.

Definition lt_dec m n : {m < n} + {n <= m} :=
    match le_dec n m with
    | left  n_le_m => right _ n_le_m
    | right m_lt_n => left  _ m_lt_n
    end.

Fixpoint bst_insert (x : nat) (t : tree nat) : tree nat :=
    match t with
    | Leaf       => Node nat (Leaf nat) x (Leaf nat)
    | Node L y R =>
        if lt_dec x y
        then Node nat (bst_insert x L) y R
        else
            if lt_dec y x
            then Node nat L y (bst_insert x R)
            else Node nat L y R
    end.


Theorem insert_bst : forall x T, BST T -> BST (bst_insert x T).
Proof.
Abort.

End tree_stuff.

End Ch1InClass.
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
