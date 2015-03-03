(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The [Term] data type, and associated core definitions.

The definition here follows the core of Chapter4.v, but could be easily adjusted. The point of this file is that we can then prove the soundness lemmas for the locally nameless stuff in LNTermSubst.v fairly generically. *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* [Coq.Classes.EquivDec] is Coq 8.3 only *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.ListSet.
Require Import Coq.Classes.EquivDec.

Require Import LNVar.

(* TODO: replace [beq_nat] by [equiv_dec] via [Coq.Classes.EquivDec.nat_eq_eqdec] to shorten proofs. *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* N.B., must use a section in order to use [Context], and must use
    [Context] instead of [Variable] if we want it to be implicit.
    However, we can't define notations inside sections if we want
    them to last. *)
Section ATerm.
Context  {Var : Set}.
Context `{VT : VarType Var}.
Implicit Type x y z : Var.
Implicit Type i j k : nat.

Context {constant : Set}.
Implicit Type c : constant.

Context {primitive : Set}.
Implicit Type p : primitive.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Grammar of pre-terms. Free variables have names; bound variables
    have de Bruijn indices. *)
Inductive Term : Set :=
    | Fvar  : Var  -> Term
    | Bvar  : nat  -> Term
    | Lam   : Term -> Term
    | App   : Term -> Term -> Term
    | Const : constant  -> Term
    | Prim  : primitive -> Term -> Term
    | If    : Term -> Term -> Term -> Term
    .
Implicit Type e f g h : Term.

Delimit Scope term_scope with Term.
Bind Scope term_scope with Term.
Open Scope term_scope.


(** Substitution for names/free-vars. Replace [Fvar x] by [e] in [f]. *)
Fixpoint fsubst x e f {struct f} : Term :=
    match f with
    | Fvar y      => if equiv_dec x y then e else f
    | Bvar i      => f
    | Lam  f1     => Lam (fsubst x e f1)
    | App  f1 f2  => App (fsubst x e f1) (fsubst x e f2)
    | Const c     => f
    | Prim p f1   => Prim p (fsubst x e f1)
    | If f1 f2 f3 => If (fsubst x e f1) (fsubst x e f2) (fsubst x e f3)
    end.
Notation "[ x ~> e ] f" := (fsubst x e f)
    (at level 0, x at level 99, right associativity) :term_scope.


(** Substitution for local/bound-vars. Replace [Bvar i] by [e] in
    [f]. The [∆∆e·f] specialization is called ``opening'' (or
    [openTerm] in the theorems); and the [∆x·f] specialization is
    called ``variable opening'' (or [openVar] in the theorems). *)
Fixpoint bsubst i e f {struct f} : Term :=
    match f with
    | Fvar x      => f
    | Bvar j      => if beq_nat i j then e else f
    | Lam  f1     => Lam (bsubst (S i) e f1)
    | App  f1 f2  => App (bsubst i e f1) (bsubst i e f2)
    | Const c     => f
    | Prim p f1   => Prim p (bsubst i e f1)
    | If f1 f2 f3 => If (bsubst i e f1) (bsubst i e f2) (bsubst i e f3)
    end.
Notation "{ i ~> e } f" := (bsubst i e f)
    (at level 0, i at level 99, right associativity) :term_scope.
Notation "∆∆ e · f"     := (bsubst 0 e f)
    (at level 67, right associativity) :term_scope.
Notation "∆ x · f"      := (bsubst 0 (Fvar x) f)
    (at level 67, right associativity) :term_scope.


(** Abstract [Fvar x] as [Bvar i] in [e]. The inverse of [bsubst],
    as it were. For a conventional named lambda, you can use [Lam(∇x·e)]. *)
Fixpoint enclose i x e {struct e} :=
    match e with
    | Fvar y      => if equiv_dec x y then Bvar i else e
    | Bvar j      => e
    | Lam  e1     => Lam (enclose (S i) x e1)
    | App  e1 e2  => App (enclose i x e1) (enclose i x e2)
    | Const c     => e
    | Prim p e1   => Prim p (enclose i x e1)
    | If e1 e2 e3 => If (enclose i x e1) (enclose i x e2) (enclose i x e3)
    end.
Notation "{ i <~ x } e" := (enclose i x e)
    (at level 0, i at level 99, right associativity) :term_scope.
Notation "∇ x · e"      := (enclose 0 x e)
    (at level 67, right associativity) :term_scope.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Well-formed terms are locally-closed pre-terms *)
Inductive LC : Term -> Prop :=
    | LCFvar  : forall x, LC (Fvar x)
    | LCLam   : forall xs t1, (forall x, x \notin xs -> LC (∆x·t1))
                -> LC (Lam t1)
    | LCApp   : forall t1 t2, LC t1 -> LC t2 -> LC (App t1 t2)
    | LCConst : forall c, LC (Const c)
    | LCPrim  : forall p t1, LC t1 -> LC (Prim p t1)
    | LCIf    : forall t1 t2 t3, LC t1 -> LC t2 -> LC t3 -> LC (If t1 t2 t3)
    .
Hint Constructors LC.


(** The return type of [LC_inv], abstracted out to reduce the size
    of types in proofs. *)
Definition LC_inv__T e (P : Term -> Prop) :=
    match e with
    | Fvar _  => forall
        (fvar : forall
            (x  : Var)
            (Ee : e = Fvar x)
            (He : LC (Fvar x))
            , P (Fvar x))
        , P e
    | Bvar _ => P e
    | Lam  _ => forall
        (lam : forall
            (xs  : set Var)
            (e1  : Term)
            (He1 : forall x (Hx : x \notin xs), LC (∆x·e1))
            (Ee  : e = Lam e1)
            (He  : LC (Lam e1))
            , P (Lam e1))
        , P e
    | App _ _ => forall
        (app : forall
            (e1  : Term) 
            (e2  : Term)
            (He1 : LC e1)
            (He2 : LC e2)
            (Ee  : e = App e1 e2)
            (He  : LC (App e1 e2))
            , P (App e1 e2))
        , P e
    | Const _ => forall
        (const : forall
            (c  : constant)
            (Ee  : e = Const c)
            (He  : LC (Const c))
            , P (Const c))
        , P e
    | Prim _ _ => forall
        (prim : forall
            (p   : primitive)
            (e1  : Term)
            (He1 : LC e1)
            (Ee  : e = Prim p e1)
            (He  : LC (Prim p e1))
            , P (Prim p e1))
        , P e
    | If _ _ _ => forall
        (ifte : forall
            (e1  : Term) 
            (e2  : Term)
            (e3  : Term)
            (He1 : LC e1)
            (He2 : LC e2)
            (He3 : LC e3)
            (Ee  : e = If e1 e2 e3)
            (He  : LC (If e1 e2 e3))
            , P (If e1 e2 e3))
        , P e
    end.

(** The non-dependent inversion tactic for [LC]. Use this lemma
    with the tactic [apply (LC_inv Ht P)]. Unfortunately, the [P]
    must generally be provided since typically it needs to do case
    analysis on [t], and [apply] isn't smart enough to figure that
    out. Consequently, the proof _script_ will be longer than just
    using [inversion Ht]; however, the proof _term_ will be
    _significantly_ shorter and more intelligible. *)
Lemma LC_inv : forall {e} (He : LC e) (P : Term -> Prop), LC_inv__T e P.
Proof.
  intros; inversion He; simpl; intros;
    [ apply fvar
    | apply (lam xs)
    | apply app
    | apply const
    | apply (prim p)
    | apply ifte
    ]; reflexivity || (subst; assumption).
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** The body of an abstraction. This is the premise to [LCLam] and
    we will prove that [forall t, LC (Lam t) <-> Body t]. *)
Definition Body e := exists xs, forall x, x \notin xs -> LC (∆x·e).
Hint Unfold Body.
Hint Transparent Body.


(** Get all the free variables in a term. *)
Fixpoint freeVars e {struct e} : set Var :=
    match e with
    | Bvar i      => \{}
    | Fvar x      => \{x}
    | Lam e1      => (freeVars e1)
    | App e1 e2   => (freeVars e1) \u (freeVars e2)
    | Const c     => \{}
    | Prim p e1   => freeVars e1
    | If e1 e2 e3 => (freeVars e1) \u (freeVars e2) \u (freeVars e3)
    end.
Notation "x \freshin e" := (x \notin (freeVars e))
    (at level 68, no associativity) :listset_scope.

End ATerm.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Notations must be (re)defined outside of sections. *)
(* BUG: the "·" are being set with too much space around them. *)

Delimit Scope term_scope with Term.
Bind Scope term_scope with Term.
Open Scope term_scope.

Notation "[ x ~> e ] f" := (fsubst x e f)
    (at level 0, x at level 99, right associativity) :term_scope.

Notation "{ i ~> e } f" := (bsubst i e f)
    (at level 0, i at level 99, right associativity) :term_scope.
Notation "∆∆ e · f"     := (bsubst 0 e f)
    (at level 67, right associativity) :term_scope.
Notation "∆ x · e"      := (bsubst 0 (Fvar x) e)
    (at level 67, right associativity) :term_scope.

Notation "{ i <~ x } e" := (enclose i x e)
    (at level 0, i at level 99, right associativity) :term_scope.
Notation "∇ x · e"      := (enclose 0 x e)
    (at level 67, right associativity) :term_scope.

Notation "x \freshin e" := (x \notin (freeVars e))
    (at level 68, no associativity) :listset_scope.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
