(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Notations for [Coq.Lists.ListSet] using the [EqDec] class.

TODO: switch to using MSets in lieu of ListSet.
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* [Coq.Classes.EquivDec] is Coq 8.3 only *)
Require Import Coq.Lists.ListSet.
Require Import Coq.Classes.EquivDec.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Notation "\{}"          := (empty_set _)
    : listset_scope.

Notation "\{ x }"       := (set_add equiv_dec x (empty_set _))
    : listset_scope.

Notation "x \a ys"      := (set_add equiv_dec x ys)
    (at level 37, right associativity) : listset_scope.

Notation "xs \u ys"     := (set_union equiv_dec xs ys)
    (at level 37, right associativity) : listset_scope.

Notation "xs \n ys"     := (set_inter equiv_dec xs ys)
    (at level 36, right associativity) : listset_scope.

Notation "xs \\ ys"     := (set_diff equiv_dec xs ys)
    (at level 34, left associativity) : listset_scope.

Notation "xs \- y"      := (set_remove equiv_dec y xs)
    (at level 34, left associativity) : listset_scope.

Notation "x \in xs"     := (set_In x xs)
    (at level 39) : listset_scope.

Notation "x \notin xs"  := (~ set_In x xs)
    (at level 39) : listset_scope.
    (* Beware of unfolding issues with [not]. *)

Delimit Scope listset_scope with set.
Bind Scope listset_scope with set.
Open Scope listset_scope.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(*
Definition Equal xs ys           := forall x:A, set_In x xs <-> set_In x ys.
Definition Subset xs ys          := forall x:A, set_In x xs -> set_In x ys.
Definition Inhab xs              := exists x:A, set_In x xs.
Definition Empty xs              := forall x:A, ~ set_In x xs.
Definition Disjoint xs ys        := forall x:A, ~ set_In x (xs \n ys).
Definition Forall (P:A->Prop) xs := forall x:A, set_In x xs -> P x.
Definition Exists (P:A->Prop) xs := exists x:A, set_In x xs /\ P x.

Notation "xs [=] ys" := (Equal xs ys)
    (at level 70, no associativity) : listset_scope.
Notation "xs [<=] ys" := (Subset xs ys)
    (at level 70, no associativity) : listset_scope.
Notation "xs \c ys" := (Subset xs ys)
    (at level 38) : listset_scope.

Theorem set_In_classical
    : forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
    (x : A) (xs : set A), ~~set_In x xs -> set_In x xs.
Proof.
  intros A eq_dec x xs; induction xs as [|x0 xs0 IHxs0]; intro H;
    [ apply H; intro H0; apply H0
    | destruct (eq_dec x x0) as [L|R];
      [ left; congruence
      | right; apply IHxs0; intro H0; apply H; intro H1; destruct H1;
        [ apply R; congruence
        | apply H0; assumption ] ] ].
Qed.
Hint Resolve set_In_classical :sets.
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
