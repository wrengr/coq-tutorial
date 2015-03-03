(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Correctness theorems for the locally nameless style.

TODO:
- [openVar_close_trivial]
- [fsubst_is_openTerm_close]

cf <http://www.chargueraud.org/softs/ln/>

*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Require Import Coq.Lists.ListSet.
Require Import WrengrUtil.Tactics.ExFalso.
Require Import WrengrUtil.Tactics.Destroy.
Require Import WrengrUtil.Tactics.Introv.
Require Import WrengrUtil.Tactics.Fequal.
Require Import WrengrUtil.CoqExtras.Nat.
Require Import WrengrUtil.CoqExtras.ListSet.

Require Import LNVar.
(* TODO: how can we parameterize this module by [LNTerm]? *)
Require Import LNTerm.
(* We assume the following API from LNTerm:
    - Term {Var} : Set
        - FVar : Var -> Term
        - BVar : nat -> Term
        - Lam  : Term -> Term
    - freeVars : Term -> set Var
        - Notation "x \freshin e" := (x \notin (freeVars e))
    - LC : Term -> Prop
    - Body : Term -> Prop
    - bsubst  : nat -> Term -> Term -> Term
        - Notation "{ j ~> e } f" := (bsubst j e f)
        - Notation "∆∆ e · f"     := (bsubst 0 e f)
        - Notation "∆ x · f"      := (bsubst 0 (FVar x) f)
    - fsubst  : Var -> Term -> Term -> Term
        - Notation "[ x ~> e ] f" := (fsubst x e f)
    - enclose : nat -> Var  -> Term -> Term
        - Notation "{ j <~ x } e" := (enclose j x e)
        - Notation "∇ x · e"      := (enclose 0 x e)
   *)


(* N.B., must use a section in order to use [Context], and must use
    [Context] instead of [Variable] if we want it to be implicit.
    However, we can't define notations inside sections if we want
    them to last. *)
Section ASubst.
Context  {Var : Set}.
Context `{VT : VarType Var}.
Context {constant  : Set}.
Context {primitive : Set}.
Implicit Type e f g : @Term Var constant primitive.
Implicit Type x y z : Var.
Implicit Type i j k : nat.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Lemmas for listset. *)

Lemma freshin_close_intro
    : forall {x y e} (N : x<>y) (Ix : x \freshin e)
    , x \freshin ∇y·e.
Proof.
  intros; generalize 0 as i; induction e; intros; simpl; auto with listset.
    destruct_if.
    
    (* HACK: why is the [in *] required for this unfold but not the other one? *)
    unfold not in *; intro H;
    apply set_union_elim in H; destruct H;
    eauto with listset.
    
    (* TODO: automate away this boring case... *)
    unfold not; intro H;
    apply set_union_elim in H; destruct H;
      [ eapply IHe1
      | apply set_union_elim in H; destruct H;
        [ eapply IHe2
        | eapply IHe3
        ]
      ]; simpl in Ix; eauto with listset.
Qed.
Hint Resolve @freshin_close_intro :listset.


Lemma freshin_close_elim
    : forall {x y e} (N : x<>y) (Ix : x \freshin ∇y·e)
    , x \freshin e.
Proof.
  intros until e; generalize 0 as i; induction e; simpl; intros;
  [ | | apply (IHe (S i)) | | | apply (IHe i) | ]; auto with listset.
  
    destruct_if in Ix; auto; intro H; inversion H; auto; congruence.
    
    (* TODO: better automation to hande these two cases... *)
    unfold not; intro H;
    apply set_union_elim in H; destruct H;
    [ apply (IHe1 i) | apply (IHe2 i) ]; auto with listset.
    
    unfold not; intro H;
    apply set_union_elim in H; destruct H;
      [ apply (IHe1 i)
      | apply set_union_elim in H; destruct H;
        [ apply (IHe2 i)
        | apply (IHe3 i)
        ]
      ]; auto with listset.
Qed.

Hint Extern 3 (?x \freshin ?e) =>
    match goal with
    | I : x \freshin (∇ ?y · e) |- _ =>
        apply (fun N => @freshin_close_elim x y e N I); congruence
    end :listset.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** [bsubst] and opening theorems. *)

Ltac auto_star :=
    try solve [ auto | eauto | intuition eauto ].

(* TODO: replace this mantra with something more efficient, like the old [if_beq_nat] or like Chargueraud's [case_nat*]. *)
Ltac if_beq_nat__mantra :=
    repeat (destruct_if; simpl); beq_nat_hyps; try ex_falso.


(** Substitution on indices is identity on well-formed terms. *)

(* N.B., the ordering of the arguments is necessary for the structure
   of the proof (i.e., the proof search). And the direction of the
   [E] equality must correlate with the direction of the resulting
   equality. *)
Lemma bsubst_trivial__core
    : forall e j g i f (N : i <> j)
    (E : {i ~> f}{j ~> g}e = {j ~> g}e)
    , {i ~> f}e = e.
Proof.
  induction e; introv N E; simpl in *;
    (* Solve the boring IH branches. The initial [auto] is to clean
       up the generated proof for [Fvar v]. All the other proofs
       are greatly uglyified by the [inversion E], but I can't think
       of a way to clean that up without loss of generality... *)
    try solve [auto; fequal; inversion E; eauto].
  
  (* The one remaining branch has interesting computational content. *)
  revert E; if_beq_nat__mantra.
Qed.


(* The direction of this equality is crucial to how we use it. *)
Theorem bsubst_trivial
    : forall i f e (He : LC e)
    , {i ~> f}e = e.
Proof.
  refine (fun i f e He => _ e He i f);
  clear       i f e He.
  (* HACK: I don't know what's magical about [induction 1] vs [induction e] *)
  induction 1; intros; simpl; fequal; auto_star.
  destruct (freshVar xs) as [x Ix].
  apply (@bsubst_trivial__core t1 0 (Fvar x)); auto_star.
Qed.


(* TODO:
Tactic Notation "reorder_induction"
    ne_simple_intropattern_list(WS)
    simple_intropattern_list(XS)
    simple_intropattern(Y)
    simple_intropattern_list(ZS)
  :=
    (* the [refine (fun WS => _ XS Y ZS); clear WS; intros XS Y] mantra generates cleaner proof terms than either [intros WS; revert ZS] or even [intros WS; refine (_ XS Y ZS); clear WS; intros XS Y]. Using [refine] introduces a spurious lambda-abstraction and application; using [revert] introduces a spurious let-binding. There should be a cleaner way still to do all this... *)
    refine (fun WS => _ XS Y ZS); clear WS; intros XS Y;
    (* The whole point of this tactic is to induct on [Y] while generalizing over [ZS]. *)
    induction Y; intros ZS;
    (* Some basic cleanup to try and handle boring IH cases. For the [Fvar] basis case, [reflexivity] is cleaner than [fequal;auto], though both work. *)
    simpl; try solve [ reflexivity | fequal; auto ].
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** [bsubst] of well-formed terms is idempotent. *)
Corollary bsubst_idempotent
    : forall i f e (Hf : LC f)
    , {i ~> f}{i ~> f}e = {i ~> f}e.
Proof.
  (* reorder_induction [i f e Hf] [f Hf] e [i]; *)
  refine (fun i f e Hf =>    _ f Hf e i);
  clear       i f e Hf; intros f Hf e;
  induction e; intro i; simpl; fequal.
    (* The one interesting case *)
    if_beq_nat__mantra; apply bsubst_trivial; exact Hf.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* There's no good way to state completeness for [bsubst].
TODO: maybe by using the [Body] definition?
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** For distinct indices, [bsubst] of well-formed terms commutes. *)
Corollary bsubst_comm
    : forall i f j g e (N : i <> j) (Hf : LC f) (Hg : LC g)
    , {i ~> f}{j ~> g}e = {j ~> g}{i ~> f}e.
Proof.
  (* reorder_induction [i f j g e N Hf Hg] [f g Hf Hg] e [i j N]; *)
  refine (fun i f j g e N Hf Hg =>    _ e f g Hf Hg i j N);
  clear       i f j g e N Hf Hg; intros e f g Hf Hg;
  induction e; intros i j N; simpl; try solve [ reflexivity | fequal; auto ].
    (* The one interesting case *)
    if_beq_nat__mantra; [|symmetry]; apply bsubst_trivial; assumption.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** [fsubst] distributes over [bsubst]. *)
Theorem fsubst_bsubst_dist
    : forall x f i g e (Hf : LC f)
    , [x ~> f]{i ~> g}e = {i ~> [x ~> f]g}[x ~> f]e.
Proof.
  (* reorder_induction [x f i g e Hf] [x f Hf g] e [i]; *)
  refine (fun x f i g e Hf =>    _ x f Hf g e i).
  clear       x f i g e Hf; intros x f Hf g e;
  induction e; intro i; simpl; fequal;
    (* TODO: incorporate this into [if_beq_nat__mantra] *)
    [ destruct_if; simpl;
      [ symmetry; apply bsubst_trivial; exact Hf
      | reflexivity
      ]
    | destruct_if; simpl; reflexivity
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Substitution distributes over the openTerm operation. *)
Corollary fsubst_openTerm_dist
    : forall x f e1 e2 (Hf : LC f)
    , [x ~> f] (∆∆e1 · e2) = ∆∆([x ~> f]e1) · ([x ~> f]e2).
Proof.
  intros. apply fsubst_bsubst_dist. exact Hf.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** For distinct names, substitution and openVar commute. *)
Corollary fsubst_openVar_comm
    : forall x y f e (N : x <> y) (Hf : LC f)
    , [y ~> f](∆x·e) = ∆x·([y ~> f]e).
Proof.
  intros.
  pose (r := fsubst_openTerm_dist y f (Fvar x) e Hf).
  assert (Hr : [y ~> f](Fvar x) = Fvar x) by (simpl; destruct_if; congruence).
  rewrite Hr in r. (* because [rewrite <- Hr at 2] requires setoid stuff. *)
  exact r.
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** [enclose] theorems. *)

(** For fresh names, closing is the identity function. *)
Theorem enclose_trivial
    : forall i x e (Ix : x \freshin e)
    , {i <~ x}e = e.
Proof.
  (* TODO: incorporate into [reorder_induction] *)
  refine (fun i x e Ix =>    _ x e Ix i);
  clear       i x e Ix; intros x e Ix.
  induction e; intro i; simpl; simpl in Ix; fequal; eauto with listset;
    [ destruct_if; ex_falso Ix by left
    (* TODO: better automation to cover these two cases... *)
    | apply IHe2; auto with listset
    | apply IHe3; auto with listset
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** After closing, the name is not free in the new term. *)
Theorem enclose_complete
    : forall i x e
    , x \freshin ({i <~ x}e).
Proof.
  (* TODO: incorporate into [reorder_induction]
  refine (fun i x e =>    _ x e i);
  clear       i x e; intros x e.
  induction e; intro i; simpl;
    [ destruct_if; simpl; intuition
    | identity
    | apply IHe
    | apply IHe
    | unfold not; intro H
    ; apply set_union_elim in H
    ; inversion H; [ apply (IHe1 i) | apply (IHe2 i) ]; assumption
    ].
  *)
  intros; revert i; induction e; intro i; simpl;
    (* handle the boring IH cases. *)
    try solve [auto];
    (* Two interesting cases left: *)
    [ destruct_if; simpl; intuition
    | unfold not; intro H; destruct (set_union_elim _ _ _ _ H); intuition eauto
    (* [destruct] is cleaner than [apply set_union_elim in H; inversion H] *)
    (* TODO: better automation to automatically cover this last case... *)
    | unfold not; intro H;
      apply set_union_elim in H; destruct H;
        [ apply (IHe1 i)
        | apply set_union_elim in H; destruct H;
          [ apply (IHe2 i)
          | apply (IHe3 i)
          ]
        ]; auto with listset
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** For distinct names, substitution and closing commute. *)
Theorem fsubst_close_comm
    : forall x y f e (N : x <> y) (Ix : x \freshin f)
    , [y ~> f](∇x·e) = ∇x·[y ~> f]e.
Proof.
  intros.
  generalize 0 as i. (* TODO: would anyone need the general lemma? *)
  induction e; intro; simpl; fequal;
    [ repeat (destruct_if; simpl); symmetry; apply enclose_trivial; exact Ix ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* N.B., you can _not_ prove this if you require [LC e]. *)
(** Opening a term and then closing it again is the identity. *)
Theorem close_openVar_trivial
    : forall x e (Ix : x \freshin e)
    , ∇x·∆x·e = e.
Proof.
  intros.
  generalize 0 as i. (* TODO: would anyone need the general lemma? *)
  induction e; intro i; simpl;
    (* handle the boring IH cases. *)
    try solve [ fequal; simpl in Ix; auto with listset ];
    (* Two interesting cases left: *)
    [ destruct_if; ex_falso Ix by left
    | destruct_if; beq_nat_hyps; simpl; [ destruct_if | reflexivity ]
    (* TODO: better automation to automatically cover this last case... *)
    | rewrite IHe1;
      [ rewrite IHe2; 
        [ rewrite IHe3;
          [ reflexivity
          |]
        |]
      |]; simpl in Ix; auto with listset
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Closing a term and then opening it again is the identity. *)

Lemma openVar_close_trivial__core
    : forall x y z e i j (Nij : i <> j) (Nzx : z <> x) (Ix : x \freshin e)
    , {i ~> Fvar x}{j ~> Fvar y}{j <~ z}e
    = {j ~> Fvar y}{j <~ z}{i ~> Fvar x}e.
Proof.
  intros until e; induction e; intros; simpl; solve
    [ if_beq_nat__mantra
    | first
      (* TODO: generalize this to work for all arities... *)
      [ apply f_equal3; [ apply IHe1 | apply IHe2 | apply IHe3 ]
      | apply f_equal2; [ apply IHe1 | apply IHe2 ]
      | apply f_equal; apply IHe
      ]; solve
        [ assumption
        | congruence
        | eauto with listset
        ]
    ].
Qed.


(*
(* BUG: with the [He] requirement, we can eliminate the [Bvar] branch, but can't come up with an [He] for the [Lam] branch. Without it, we can solve the [Lam] branch but not the [Bvar] branch... *)
Theorem openVar_close_trivial
    : forall x e (Ix : x \freshin e) (He : LC e)
    , ∆x·∇x·e = e.
Proof.
  intros.
  generalize 0 as i. (* TODO: would anyone need the general lemma? *)
  induction e; intro i; simpl.
    destruct_if; simpl;
      [ destruct_if; beq_nat_hyps; ex_falso__neq_self_hyp
      | reflexivity
      ].
    
    (* Or else prove |- (if beq_nat i n then Fvar x else Bvar n) = Bvar n *)
    apply (LCBvar_absurd He).
    
    (* Or else [apply f_equal; apply IHe; exact Ix] *)
    apply f_equal.
    apply (LC_inv He (fun e0 =>
      match e0 with
      | Lam _ e1 => _ e1
      | _        => False
      end)).
    intros.
    _
    
    apply f_equal; apply IHe;
      eauto with listset;
      apply proj_LCBrak in He; assumption.
    
    apply f_equal2; [ apply IHe1 | apply IHe2 ];
      eauto with listset;
      [ apply proj1_LCJuxt in He | apply proj2_LCJuxt in He ]; assumption.
Qed.

Theorem openVar_close_trivial
    : forall x e (Ix : x \freshin e) (He : LC e)
    , ∆x·∇x·e = e.
Proof.
  intros; generalize 0 as i; induction e; intros;
  simpl in *; auto_star; fequal; auto_star;
  [ | | | apply IHe | apply IHe1 | apply IHe2 ];
  eauto with listset; inversion He; auto_star. (* TODO: [LC_inv] *)
    destruct_if; simpl;
      [ destruct_if; beq_nat_hyps; auto_star
      | reflexivity
      ].
    _
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* From right to left, this one is essentially the alpha-variance rule. *)
(** Renaming a free variable via [fsubst] and then closing over the
    new variable, is the same as just closing over the old variable. *)
Theorem close_rename
    : forall x y e (Ix : x \freshin e)
    , ∇x·[y ~> Fvar x]e = ∇y·e.
Proof.
  intros.
  generalize 0 as i. (* TODO: would anyone need the general lemma? *)
  induction e; intro i; simpl;
    (* Handle the boring IH cases. The [simpl] is unnecessary, but
       cleans up the proof considerably in the [Juxt] case. Also,
       the [Juxt] case is the one that requires [eauto] instead of
       just [auto], though I'm not entirely sure why... *)
    try solve [ simpl in Ix; fequal; eauto with listset ];
      (* One interesting case left, and one boring case *)
      [ destruct_if; simpl; destruct_if; ex_falso Ix by left
      (* TODO: better automation to handle this boring case... *)
      | rewrite IHe1; try assumption;
        [ rewrite IHe2; try assumption;
          [ rewrite IHe3; try assumption;
            [ reflexivity
            |]
          |]
        |]; simpl in Ix; auto with listset
      ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** [fsubst] theorems. *)

(** After substitution, the name is not free in the new term. *)
Theorem fsubst_complete
    : forall x f e (Ix : x \freshin f)
    , x \freshin ([x ~> f]e).
Proof.
  intros; induction e; simpl;
    (* Handle the boring IH cases. *)
    try solve [auto];
    (* Two interesting cases left, and one boring case *)
    [ destruct_if; unfold not; intro H; inversion H; congruence
    | unfold not; intro H; destruct (set_union_elim _ _ _ _ H); auto
    (* [destruct] is cleaner than [apply set_union_elim in H; inversion H] *)
    
    (* TODO: better automation to handle this boring case... *)
    | unfold not; intro H;
      apply set_union_elim in H; destruct H;
        [ apply IHe1
        | apply set_union_elim in H; destruct H;
          [ apply IHe2
          | apply IHe3
          ]
        ]; auto with listset
    ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Substitution for a fresh name is identity. *)
Theorem fsubst_trivial
    : forall x f e (Ix : x \freshin e)
    , [x ~> f]e = e.
Proof.
  intros. induction e; simpl;
    (* Handle the boring IH cases. The [simpl] is unnecessary, but
       cleans up the proof considerably in the [Juxt] case. Also,
       the [Juxt] case is the one that requires [eauto] instead of
       just [auto], though I'm not entirely sure why... *)
    try solve [ simpl in Ix; fequal; eauto with listset ];
    (* One interesting case left, and one boring case *)
      [ destruct_if; ex_falso Ix by left
      (* TODO: better automation to handle this boring case... *)
      | rewrite IHe1; try assumption;
        [ rewrite IHe2; try assumption;
          [ rewrite IHe3; try assumption;
            [ reflexivity
            |]
          |]
        |]; simpl in Ix; auto with listset
      ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Substitution is idempotent. *)
Corollary fsubst_idempotent
    : forall x f e (Ix : x \freshin f)
    , [x ~> f][x ~> f]e = [x ~> f]e.
Proof.
  intros. induction e; simpl; fequal;
    [ destruct_if; simpl; [ apply fsubst_trivial; exact Ix | destruct_if ]].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** For distinct names, [fsubst] commutes. *)
Theorem fsubst_comm
    : forall x f y g e (N : x <> y) (Ix : x \freshin g) (Iy : y \freshin f)
    , [x ~> f][y ~> g]e = [y ~> g][x ~> f]e.
Proof.
  intros. induction e; simpl; [|fequal..]; (* why do we need hand-holding? *)
    [ if_beq_nat__mantra; [|symmetry]; apply fsubst_trivial; assumption ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** [fsubst] distributes over itself. *)
Theorem fsubst_dist
    : forall x f y g e (N : x <> y) (Iy : y \freshin f)
    , [x ~> f][y ~> g]e = [y ~> [x ~> f]g][x ~> f]e.
Proof.
  intros; induction e; simpl; [|fequal..]; (* why do we need hand-holding? *)
    [ if_beq_nat__mantra; rewrite fsubst_trivial; auto ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Renaming a free variable via [fsubst] and then substituting for
    the new variable, is the same as just substituting for the old
    variable. *)
Theorem fsubst_rename
    : forall x y e f (Iy : y \freshin e)
    , [y ~> f][x ~> Fvar y]e = [x ~> f]e.
Proof.
  intros; induction e; simpl;
    (* Handle the boring IH cases. The [simpl] is unnecessary, but
       cleans up the proof considerably in the [Juxt] case. Also,
       the [Juxt] case is the one that requires [eauto] instead of
       just [auto], though I'm not entirely sure why... *)
    try solve [ simpl in Iy; fequal; eauto with listset ];
    (* One interesting case left, and one boring case *)
    (* TODO: incorporate this into the [if_beq_nat__mantra] *)
      [ destruct_if; simpl;
        [ destruct_if; beq_nat_hyps; ex_falso
        | destruct_if; ex_falso Iy by left
        ]
      (* TODO: better automation to handle this boring case... *)
      | rewrite IHe1; try assumption;
        [ rewrite IHe2; try assumption;
          [ rewrite IHe3; try assumption;
            [ reflexivity
            |]
          |]
        |]; simpl in Iy; auto with listset
      ].
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* This should be a consequence of [fsubst_bsubst] with [g:=Fvar x]
    by exploiting [fsubst_trivial]. However, doing so also requires
    an additional assumption about the local closure of "the term
    being substituted in" which isn't necessary in the direct
    definition. *)

(** Opening up an abstraction of body [e] with a term [f] is the
    same as opening up the abstraction with a fresh name [x] and
    then substituting [f] for [x]. *)
Theorem fsubst_intro
    : forall x f e (Ix : x \freshin e) (Hf : LC f)
    , ∆∆f·e = [x ~> f](∆x·e).
Proof.
  intros.
  generalize 0 as i. (* TODO: would anyone need the general lemma? *)
  induction e; intro i; simpl;
    (* Handle the boring IH cases. The [simpl] is unnecessary, but
       cleans up the proof considerably in the [Juxt] case. Also,
       the [Juxt] case is the one that requires [eauto] instead of
       just [auto], though I'm not entirely sure why... *)
    try solve [ simpl in Ix; fequal; eauto with listset ];
    (* Two interesting cases left, and one boring case *)
    [ destruct_if; ex_falso Ix by left
    | destruct n; simpl; repeat (destruct_if; simpl); reflexivity
    (* TODO: better automation to handle this boring case... *)
    | rewrite IHe1; try assumption;
      [ rewrite IHe2; try assumption;
        [ rewrite IHe3; try assumption;
          [ reflexivity
          |]
        |]
      |]; simpl in Ix; auto with listset
    ].
Qed.


(* TODO: is there a proof without [Ix], [Hf], or [He]? Because it's silly with [Ix]... There must be a way without [openVar_close_trivial] then... Maybe with [fsubst_rename]? The [Hf] is requisite if this is to be a corollary of [fsubst_intro]; and [Ix] (or [Iy]?) also.

Corollary fsubst_is_openTerm_close
    : forall x f e (Ix : x \freshin e) (Hf : LC f) (He : LC e)
    , [x ~> f]e = ∆∆f·∇x·e.
Proof.
  intros.
  rewrite (fsubst_intro x); auto.
    rewrite openVar_close_trivial; auto.
    
    apply enclose_complete.
Qed.

Corollary fsubst_is_openTerm_close
    : forall x f e (Hf : LC f)
    , [x ~> f]e = ∆∆f·∇x·e.
Proof.
  fix 3.
  intros.
  destruct (freshVar (x \a freeVars f \u freeVars e)) as (y, Iy).
  rewrite (fsubst_intro y); auto.
    rewrite <- fsubst_is_openTerm_close.
      rewrite fsubst_rename; auto with listset.
      
      apply LCFvar.
    
    apply freshin_close_intro; unfold not in *; intro; apply Iy; auto with listset.
Abort.(* ill-formed recursion. *)

Proof.
  intros.
  generalize 0 as i.
  induction e; intro; simpl.
    destruct_if; simpl.
      destruct_if; beq_nat_hyps; ex_falso.
      reflexivity.
    
    destruct_if.
    beq_nat_hyps.
    (* HeqB : i = n  |-  Bvar n = f *)
    
    apply f_equal; apply IHe.
    
    apply f_equal; apply IHe.
    
    apply f_equal2; [ apply IHe1 | apply IHe2 ].
Abort.
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Stability under substitution *)

(** Terms are stable under substitution. *)
Theorem LC_fsubst
    : forall x f e (Hf : LC f) (He : LC e)
    , LC ([x ~> f]e).
Proof.
  intros. induction He; simpl; (* N.B., that's induction on [He] not [e]! *)
    (* Handle the boring cases *)
    try solve [constructor; assumption];
    (* Two interesting cases remain *)
    [ destruct_if; apply LCFvar
    | apply (LCLam (x \a xs)) (* we add [x] to discharge [x<>x0] later. *)
    ; intros x0 Ix0
    ; rewrite <- fsubst_openVar_comm; [ | auto with listset | exact Hf ]
    ; apply H0
    ; auto with listset
    ].
Qed.

Hint Resolve LC_fsubst.


(** Bodies are stable under substitution. *)
Corollary Body_fsubst
    : forall x f e (Hf : LC f) (He : Body e)
    , Body ([x ~> f]e).
Proof.
  intros.
  destruct He as (xs, Hxs).
  exists (x \a xs).
  intros x0 Ix0.
  rewrite <- fsubst_openVar_comm;
    [ apply LC_fsubst; [ exact Hf | apply Hxs; auto with listset ]
    | intuition
    | exact Hf
    ].
Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** ** Stability under opening *)

(** Conversion from locally closed abstractions to bodies. *)
Lemma Body_from_LCLam : forall e, LC (Lam e) -> Body e.
Proof.
(*
(* Short and sweet, but larger proof term... *)
  intros. inversion H. exists xs. assumption.
*)
(* longer script, but shorter proof term... *)
  intros e H.
  apply (LC_inv H
    (fun e0 => match e0 with | Lam e1 => Body e1 | _ => False end)).
  intros.
  exists xs.
  assumption.
Qed.


(** Conversion from bodies to locally closed abstractions. *)
Lemma LCLam_from_Body : forall e, Body e -> LC (Lam e).
Proof.
  intros e H. destruct H as [xs Hxs]. exact (LCLam xs e Hxs).
Qed.

Hint Resolve Body_from_LCLam LCLam_from_Body.


(** Opening a body with a term gives a term. *)
Lemma LC_openTerm
    : forall f e (Hf : LC f) (He : Body e)
    , LC (∆∆f·e).
Proof.
  intros.
  destruct He as [xs Hxs].
  destruct (freshVar (xs \u freeVars e)) as [x Ix].
  rewrite (fsubst_intro x); [ | auto with listset | exact Hf ].
  apply LC_fsubst; [ exact Hf | apply Hxs; auto with listset ].
Qed.
    

(** Opening a body with a free variable gives a term. *)
Corollary LC_openVar
    : forall x e (He : Body e)
    , LC (∆x·e).
Proof.
  intros. apply LC_openTerm; [ apply LCFvar | exact He ].
Qed.

Hint Resolve LC_openVar LC_openTerm.

End ASubst.
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
