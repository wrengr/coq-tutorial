(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Finite maps from variables/names, for use with the locally nameless style. *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* [Coq.Classes.EquivDec] is Coq 8.3 only *)
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Require Import WrengrUtil.CoqExtras.ListSet.
Require Export LNSet.
Require Export LNVar.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section LNVarMap.
Context  {Var : Set}.
Context `{VT : VarType Var}.
Implicit Type x y z : Var.

Context  {A : Type}.
Implicit Type a b c : A.


(* TODO: abstract over the fact that we're implementing [VarMap] with [list]. *)
Definition VarMap := list (Var * A).
Implicit Type ρ Γ : VarMap.


Fixpoint assoc_dom Γ : set Var :=
    match Γ with
    | nil       => \{}
    | (x,_)::Γ' => x \a assoc_dom Γ'
    end.


Fixpoint lookup x Γ : option A :=
    match Γ with
    | nil          => None
    | (y,a)::Γ' =>
        if equiv_dec x y
        then Some a
        else lookup x Γ'
    end.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Lemma lookup_app
    : forall {Γ} Γ' {x a}
    ,  lookup x Γ = Some a
    -> lookup x (Γ++Γ') = Some a.
Proof.
  intros Γ; induction Γ as [| (y,b) Γ IHΓ]; simpl; intros Γ' x a H;
    [ discriminate H
    | destruct (equiv_dec x y); [| apply IHΓ ]; assumption
    ].
Qed.


(* BUG: why can't we use the [[(x,a)]] notation here?! *)
Lemma lookup_app_none
    : forall {Γ x} a
    ,  lookup x Γ = None
    -> lookup x (Γ ++ ((x,a)::nil)) = Some a.
Proof.
  intros Γ; induction Γ as [| (y,b) Γ IHΓ]; simpl; intros x a H;
    [ destruct (equiv_dec x x); congruence
    | destruct (equiv_dec x y); [ discriminate | apply IHΓ; assumption ]
    ].
Qed.


Lemma not_dom_lookup_none
    : forall {Γ x}
    ,  x \notin assoc_dom Γ
    -> lookup x Γ = None.
Proof.
  intros Γ; induction Γ as [| (y,b) Γ IHΓ]; simpl; intros x H;
    [ reflexivity
    | destruct (equiv_dec x y);
      [ contradiction H | apply IHΓ ];
      auto with listset
    ].
Qed.


Lemma lookup_dom
    : forall {Γ x a}
    ,  lookup x Γ = Some a
    -> x \in assoc_dom Γ.
Proof.
  intros Γ; induction Γ as [| (y,b) Γ IHΓ]; simpl; intros x a H;
    [ discriminate
    | destruct (equiv_dec x y); [| pose (IHΓ _ _ H) ]; auto with listset
    ].
Qed.


End LNVarMap.

(* Undo the implicitness of [Var] and [A] for [VarMap]. *)
Implicit Arguments VarMap [].


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section DerivedOperations.
Context  {Var : Set}.
Context `{VT : VarType Var}.
Context  {exp : Type}.
Context  {ty  : Type}.
Implicit Type x : Var.
Implicit Type e : exp.
Implicit Type t : ty.

Definition env := VarMap Var exp.
Implicit Type ρ : env.

Definition ty_env := VarMap Var ty.
Implicit Type Γ : ty_env.

Inductive pointwise (R : exp -> ty -> Prop) : ty_env -> env -> Prop :=
    | pointwise_nil
        : pointwise R nil nil
    | pointwise_cons
        : forall Γ ρ x e t
        ,  R e t
        -> pointwise R Γ ρ
        -> pointwise R ((x,t)::Γ) ((x,e)::ρ)
    .

End DerivedOperations.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
