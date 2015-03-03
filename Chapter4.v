(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Chapter4

This file is a translation of Chapter4.thy as of 2015-03-02T14:11:15-05:00
(TODO: get the git version number or whatever). We only translate
the code, not the actual text of the chapter.
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.ZArith_dec.
Require Import Coq.Classes.EquivDec.
Require Import Omega.

Require Import WrengrUtil.Relations.Core.
Require Import WrengrUtil.CoqExtras.ListSet.
Require Import LNVar.
Require Import LNVarMap.

(* For [le_dec] and [lt_dec] *)
Require Import Chapter1.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section Chapter4.
(* We assume some arbitary definition of variables in this section. *)
Context  {Var : Set}.
Context `{VT : VarType Var}.


Inductive const : Set :=
    | IntC  : Z    -> const
    | BoolC : bool -> const
    .

Inductive primitive : Set := Inc | Dec | Neg | IsZero | Not.

Inductive prim_result : Set :=
    | Result : const -> prim_result
    | PError : prim_result
    .

Definition eval_prim (p:primitive) (c:const) : prim_result :=
    match p, c with
    | Inc,    IntC n  => Result (IntC (Zsucc n))
    | Dec,    IntC n  => Result (IntC (Zpred n))
    | Neg,    IntC n  => Result (IntC (Zopp n))
    | IsZero, IntC n  => Result (BoolC (if Z_eq_dec n 0 then true else false))
    | Not,    BoolC b => Result (BoolC (negb b))
    | _, _            => PError
    end.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section STLC_with_De_Bruijn_Indices.

Inductive db_exp :=
    | DBConst : const                      -> db_exp
    | DBPrim  : primitive -> db_exp        -> db_exp
    | DBIf    : db_exp -> db_exp -> db_exp -> db_exp
    | DBVar   : nat                        -> db_exp
    | DBLam   : db_exp                     -> db_exp
    | DBApp   : db_exp -> db_exp           -> db_exp
    .

(* TODO: syntax "\<up>_ _" [80,80]79 *)
Fixpoint shift (c:nat) (e:db_exp) : db_exp :=
    match e with
    | DBConst k     => DBConst k
    | DBPrim p e    => DBPrim p (shift c e)
    | DBIf e1 e2 e3 => DBIf (shift c e1) (shift c e2) (shift c e3)
    | DBVar k       => if lt_dec k c then DBVar k else DBVar (S k)
    | DBLam e       => DBLam (shift (S c) e)
    | DBApp e1 e2   => DBApp (shift c e1) (shift c e2)
    end.


(* TODO: syntax "{_\<mapsto>_}_" [54,54,54]53 *)
Fixpoint db_subst  (j:nat) (e:db_exp) (f:db_exp) : db_exp :=
    match f with
    | DBConst c     => DBConst c
    | DBPrim p e'   => DBPrim p (db_subst j e e')
    | DBIf e1 e2 e3 => DBIf (db_subst j e e1) (db_subst j e e2) (db_subst j e e3)
    | DBVar k       => if eq_nat_dec k j then e else DBVar k
    | DBLam e'      => DBLam (db_subst (S j) (shift 0 e) e')
    | DBApp e1 e2   => DBApp (db_subst j e e1) (db_subst j e e2)
    end.

(* TODO: syntax "\<longmapsto>db" 70 *)
Inductive reduce_fb_db : db_exp -> db_exp -> Prop :=
    | beta_db
        : forall e e'
        , reduce_fb_db (DBApp (DBLam e) e') (db_subst 0 e' e)
    | c_lambda_db
        : forall e e'
        , reduce_fb_db e e'
        -> reduce_fb_db (DBLam e) (DBLam e')
    | c_app1_fb_db
        : forall e1 e1' e2
        , reduce_fb_db e1 e1'
        -> reduce_fb_db (DBApp e1 e2) (DBApp e1' e2)
    | c_app2_fb_db
        : forall e1 e2 e2'
        , reduce_fb_db e2 e2'
        -> reduce_fb_db (DBApp e1 e2) (DBApp e1 e2')
    | r_prim_fb_db
        : forall p c c'
        , eval_prim p c = Result c'
        -> reduce_fb_db (DBPrim p (DBConst c)) (DBConst c')
    | c_prim_fb_db
        : forall p e e'
        , reduce_fb_db e e'
        -> reduce_fb_db (DBPrim p e) (DBPrim p e')
    | r_if_true_fb_db
        : forall e2 e3
        , reduce_fb_db (DBIf (DBConst (BoolC true)) e2 e3) e2
    | r_if_false_fb_db
        : forall e2 e3
        , reduce_fb_db (DBIf (DBConst (BoolC false)) e2 e3) e3
    | c_if1_fb_db
        : forall e1 e1' e2 e3
        , reduce_fb_db e1 e1'
        -> reduce_fb_db (DBIf e1 e2 e3) (DBIf e1' e2 e3)
    | c_if2_fb_db
        : forall e1 e2 e2' e3
        , reduce_fb_db e2 e2'
        -> reduce_fb_db (DBIf e1 e2 e3) (DBIf e1 e2' e3)
    | c_if3_fb_db
        : forall e1 e2 e3 e3'
        , reduce_fb_db e3 e3'
        -> reduce_fb_db (DBIf e1 e2 e3) (DBIf e1 e2 e3')
    .
(* TODO: do we want to add hints about using these as intro rules? *)

End STLC_with_De_Bruijn_Indices.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section STLC_with_Locally_Nameless.

Inductive exp :=
    | Const   : const -> exp
    | Prim    : primitive -> exp -> exp
    | IfE     : exp -> exp -> exp -> exp
    | FVar    : Var -> exp (* use our abstract [Var] type *)
    | BVar    : nat -> exp
    | LambdaE : exp -> exp
    | AppE    : exp -> exp -> exp
    .
Delimit Scope exp_scope with exp.
Bind Scope exp_scope with exp.
Open Scope exp_scope.


Definition list_max : list nat -> nat :=
    list_rec (fun _ => nat) 0 (fun x _xs m => max x m).


(* Why isn't this in the standard library? *)
Lemma zero_lt : forall {x y}, x < y -> 0 < y.
Proof.
  intros; destruct (eq_nat_dec 0 x); [ subst; assumption | omega ].
Qed.


(* Why isn't this in the standard library? *)
Lemma max_lt : forall {x y z}, max x y < z -> x < z /\ y < z.
Proof.
  intro x; induction x; simpl.
    intros y z y_lt_z; split;
      [ eapply zero_lt; eassumption
      | exact y_lt_z
      ].
    
    intros y z H; destruct y; simpl in *.
      destruct z.
        inversion H. (* absurd *)
        
        apply lt_S_n in H.
        split; omega.
      
      destruct z.
        inversion H. (* absurd *)
        
        apply lt_S_n in H.
        destruct (IHx y z H).
        split; omega.
Qed.
  
    
Lemma list_max_fresh : forall {n xs} , list_max xs < n -> ~In n xs.
Proof.
  intros n xs.
  revert n.
  induction xs; simpl; intros n H.
    auto.
    
    destruct (max_lt H) as [H0 H1].
    intro H2; destruct H2.
      omega. (* absurd *)
      
      exact (IHxs n H1 H2). (* or: [eapply IHxs; eassumption.] *)
Qed.


Definition mklet (e1:exp) (e2:exp) : exp := AppE (LambdaE e2) e1.


(* Coq's [app] function has the notation [++], which is like Isabelle's [@] *)
(* But we use [set] with our LNSet notation, instead of using [list]. *)
Fixpoint FV (e:exp) : set Var :=
    match e with
    | Const c      => \{}
    | Prim p e     => FV e
    | IfE e1 e2 e3 => FV e1 \u FV e2 \u FV e3
    | FVar y       => \{y}
    | BVar k       => \{}
    | LambdaE e    => FV e
    | AppE e1 e2   => FV e1 \u FV e2
    end.

End STLC_with_Locally_Nameless.

Notation "x \freshin e" := (x \notin (FV e))
    (at level 68, no associativity) :listset_scope.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section Dynamic_Semantics_via_an_Interpreter.

(** Substitution for local/bound-vars. Replace [BVar j] by [e] in [f]. The [∆∆e·f] specialization is called ``opening'' (or [openTerm] in the theorems); and the [∆x·f] specialization is called ``variable opening'' (or [openVar] in the theorems). *)
Fixpoint bsubst (j:nat) (e:exp) (f:exp) : exp :=
    match f with
    | Const c      => Const c
    | Prim p e'    => Prim p (bsubst j e e')
    | IfE e1 e2 e3 => IfE (bsubst j e e1) (bsubst j e e2) (bsubst j e e3)
    | FVar x       => FVar x
    | BVar k       => if eq_nat_dec k j then e else BVar k
    | LambdaE e'   => LambdaE (bsubst (S j) e e')
    | AppE e1 e2   => AppE (bsubst j e e1) (bsubst j e e2)
    end.
(* Notation was ("{_\<rightarrow>_}_" [54,54,54]53) in Isabelle/HOL *)
(* HACK: we use double braces instead of single braces to avoid conflict with the notation for, e.g., sumbool. *)
Notation "{{ j ~> e }} f" := (bsubst j e f)
    (at level 0, j at level 99, right associativity) :exp_scope.
(* Caveat: wide unicode characters like [·] can be especially problematic to display in the terminal... *)
Notation "∆∆ e · f"     := (bsubst 0 e f)
    (at level 67, right associativity) :exp_scope.
Notation "∆ x · f"      := (bsubst 0 (FVar x) f)
    (at level 67, right associativity) :exp_scope.


(** Substitution for names/free-vars. Replace [FVar x] by [e] in [f]. *)
Fixpoint subst (x:Var) (e:exp) (f:exp) : exp :=
    match f with
    | Const c      => Const c
    | Prim p e1    => Prim p (subst x e e1)
    | IfE e1 e2 e3 => IfE (subst x e e1) (subst x e e2) (subst x e e3)
    | FVar y       => if equiv_dec x y then e else FVar y
    | BVar k       => BVar k
    | LambdaE e1    => LambdaE (subst x e e1)
    | AppE e1 e2   => AppE (subst x e e1) (subst x e e2)
    end.
(* Notation was ("[_\<mapsto>_] _" [72,72,72]71) in Isabelle/HOL *)
(* HACK: we use double brackets instead of single braces to avoid conflict with the notation for, e.g., lists. *)
Notation "[[ x ~> e ]] f" := (subst x e f)
    (at level 0, x at level 99, right associativity) :exp_scope.


Lemma subst_id : forall x v e, ~set_In x (FV e) -> subst x v e = e.
Proof.
  intros; induction e; simpl in *; auto.
    rewrite IHe; [ reflexivity | assumption ].
    
    rewrite IHe1.
      rewrite IHe2.
        rewrite IHe3.
          reflexivity.
          solve [auto with listset].
        solve [auto with listset].
      solve [auto with listset].
    
    destruct (equiv_dec x v0).
      elimtype False; apply H; left; congruence.
      
      reflexivity.
    
    rewrite IHe.
      reflexivity.
      assumption.
      
    rewrite IHe1.
      rewrite IHe2.
        reflexivity.
        solve [auto with listset].
      solve [auto with listset].
Qed.


Definition env := VarMap Var exp.
Implicit Type ρ : env.


(* TODO: notation "[_] _" [72,72]71 *)
Fixpoint msubst (ρ : env) (e : exp) : exp :=
    match ρ with
    | nil       => e
    | (x,v)::ρ' => msubst ρ' (subst x v e)
    end.


(* Caveat: displaying unicode characters like [ρ] might be a problem depending on your terminal... *)
Lemma msubst_id :
    forall ρ e,
    (forall x, x \notin (assoc_dom ρ \n FV e)) ->
    msubst ρ e = e.
Proof.
  intro ρ; induction ρ; simpl; intros e H.
    reflexivity.
    
    destruct a; simpl in *.
    rewrite IHρ.
      apply subst_id.
      intro; apply (H v).
      solve [auto with listset].
      
      intros x H0.
      apply (H x).
Abort. (* TODO *)



Inductive result :=
    | Res     : exp -> result
    | Error   : result
    | TimeOut : result
    .


Fixpoint interp (e0:exp) (n0:nat) : result :=
    match e0, n0 with
    | Const c,  S n => Res (Const c)
    | Prim p e, S n =>
        match interp e n with
        | Res (Const c) =>
            match eval_prim p c with
            | Result c' => Res (Const c')
            | PError    => Error
            end
        | Res _   => Error (* N.B., this case wasn't covered in Isabelle!! *)
        | Error   => Error
        | TimeOut => TimeOut
        end
    | IfE e1 e2 e3, S n =>
        match interp e1 n with
        | Res (Const (BoolC true))  => interp e2 n
        | Res (Const (BoolC false)) => interp e3 n
        | _                         => Error
        end
    | FVar x,     S n => Error
    | BVar k,     S n => Error
    | LambdaE e,  S n => Res (LambdaE e)
    | AppE e1 e2, S n =>
        match interp e1 n, interp e2 n with
        | Res (LambdaE e), Res v   => interp (bsubst 0 v e) n
        | TimeOut,         _       => TimeOut
        | _,               TimeOut => TimeOut
        | _,               _       => Error
      end
    | _, 0 => TimeOut
    end.


(* Note how we've translated Isabelle's [\<longrightarrow>] here. *)
Lemma inv_interp_if
    :  forall e1 e2 e3 n' v P
    ,  interp (IfE e1 e2 e3) n' = Res v
    -> (forall n b
        ,  n' = S n
        -> interp e1 n = Res (Const (BoolC b))
        -> (if b then interp e2 n =  Res v else interp e3 n = Res v)
        -> P)
    -> P.
Proof.
  (* all the discrimination on H is to prune off impossible branches. We could also use [inversion] instead of [distriminate]. *)
  intros.
  destruct n'; simpl in *; try solve [discriminate H].
  remember (interp e1 n'). (* Introduces an equality, needed for #1 *)
  destruct r; try solve [discriminate H].
  destruct e; try solve [discriminate H].
  destruct c; try solve [discriminate H].
  apply (X n' b). (* N.B., if we change P to (P:Prop) then X becomes H0 *)
    reflexivity.
    
    symmetry; assumption. (* #1 *)
    
    destruct b; assumption.
Qed.


Lemma inv_interp_app
    : forall e1 e2 n' v P
    , interp (AppE e1 e2) n' = Res v
    -> (forall n e v2
        , n' = S n
        -> interp e1 n = Res (LambdaE e)
        -> interp e2 n = Res v2
        -> interp (bsubst 0 v2 e) n = Res v
        -> P)
    -> P.
Proof.
  intros.
  destruct n'; simpl in *; try solve [discriminate H].
  (* N.B., we want semicolons here! Otherwise we'll have to repeat ourselves *)
  remember (interp e1 n'); destruct r; try solve [discriminate H];
  remember (interp e2 n'); destruct r; try solve [discriminate H]; 
  destruct e; try solve [discriminate H];
  apply (X n' e e0); congruence.
Qed.


(* Yuck! this proof needs major cleaning!! *)
Lemma interp_mono
    : forall m e n v, m <= n -> interp e m = Res v -> interp e n = Res v.
Proof.
  intro m; induction m as [| m'];
  intros e n v m_le_n H;
  destruct e; simpl in H;
  (* eight cases total; three are absurd *)
  try solve [discriminate H];
  (* five cases remain. In each case we destruct [n] so we can compute one step. *)
  (case_eq n; simpl; intros;
    [ elimtype False; omega
    | subst n; apply le_S_n in m_le_n
    ]).
    
      assumption.
      
      remember (interp e m'); destruct r; try solve [discriminate H].
      destruct e0; try solve [discriminate H].
      remember (eval_prim p c); destruct p0; try solve [discriminate H].
      rewrite (IHm' e n0 (Const c) m_le_n (eq_sym Heqr)).
      rewrite <- Heqp0.
      exact H.
      
      remember (interp e1 m'); destruct r; try solve [discriminate H].
      destruct e; try solve [discriminate H].
      destruct c; try solve [discriminate H].
      rewrite (IHm' e1 n0 (Const (BoolC b)) m_le_n (eq_sym Heqr)).
      destruct b; apply IHm'; auto.
      
      assumption.
      
      (* N.B., semicolons! and destructing [interp e2 m'] before [e] *)
      remember (interp e1 m'); destruct r; try solve [discriminate H];
      remember (interp e2 m'); destruct r; try solve [discriminate H];
      destruct e; try solve [discriminate H].
      rewrite (IHm' e1 n0 (LambdaE e) m_le_n (eq_sym Heqr)).
      rewrite (IHm' e2 n0 e0 m_le_n (eq_sym Heqr0)).
      apply IHm'; auto.
Qed.

End Dynamic_Semantics_via_an_Interpreter.

(* HACK: have to repeat notations once we close the section *)
Notation "{{ j ~> e }} f" := (bsubst j e f)
    (at level 0, j at level 99, right associativity) :exp_scope.
Notation "∆∆ e · f"     := (bsubst 0 e f)
    (at level 67, right associativity) :exp_scope.
Notation "∆ x · f"      := (bsubst 0 (FVar x) f)
    (at level 67, right associativity) :exp_scope.
Notation "[[ x ~> e ]] f" := (subst x e f)
    (at level 0, x at level 99, right associativity) :exp_scope.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section Reduction_Semantics.
Open Scope exp_scope. (* need to reopen since the old section was closed *)

(** Abstract [FVar x] as [BVar i] in [e]. The inverse of [bsubst],
    as it were. For a conventional named lambda, you can use [Lam(∇x·e)]. *)
Fixpoint close (j:nat) (x:Var) (e:exp) : exp :=
    match e with
    | Const c      => Const c
    | Prim p e'    => Prim p (close j x e')
    | IfE e1 e2 e3 => IfE (close j x e1) (close j x e2) (close j x e3)
    | FVar y       => if equiv_dec x y then BVar j else FVar y
    | BVar k       => BVar k
    | LambdaE e'   => LambdaE (close (S j) x e')
    | AppE e1 e2   => AppE (close j x e1) (close j x e2)
    end.
(* Notation was ("{_\<leftarrow>_}_" [54,54,54] 53) in Isabelle/HOL *)
Notation "{{ j <~ x }} e" := (close j x e)
    (at level 0, j at level 99, right associativity) :exp_scope.
Notation "∇ x · e"      := (close 0 x e)
    (at level 67, right associativity) :exp_scope.


(* Notation was (infix "\<longmapsto>fb" 70) in Isabelle/HOL *)
Inductive reduce_fb : exp -> exp -> Prop :=
    | full_beta
        : forall e e'
        , reduce_fb (AppE (LambdaE e) e') (∆∆e'·e)
    | c_lambda
        (* N.B., for soundness sake, beware how [x] is quantified! *)
        : forall x e e'
        ,  x \freshin e
        -> reduce_fb (∆x·e)  e'
        -> reduce_fb (LambdaE e) (LambdaE (∇x·e'))
    | c_app1_fb
        : forall e1 e1' e2
        ,  reduce_fb e1 e1'
        -> reduce_fb (AppE e1 e2) (AppE e1' e2)
    | c_app2_fb
        : forall e1 e2 e2'
        ,  reduce_fb e2 e2'
        -> reduce_fb (AppE e1 e2) (AppE e1 e2')
    | r_prim_fb
        : forall p c c'
        ,  eval_prim p c = Result c'
        -> reduce_fb (Prim p (Const c)) (Const c')
    | c_prim_fb
        : forall p e e'
        ,  reduce_fb e e'
        -> reduce_fb (Prim p e) (Prim p e')
    | r_if_true_fb
        : forall e2 e3
        , reduce_fb (IfE (Const (BoolC true)) e2 e3) e2
    | r_if_false_fb
        : forall e2 e3
        , reduce_fb (IfE (Const (BoolC false)) e2 e3) e3
    | c_if1_fb
        : forall e1 e1' e2 e3
        ,  reduce_fb e1 e1'
        -> reduce_fb (IfE e1 e2 e3) (IfE e1' e2 e3)
    | c_if2_fb
        : forall e1 e2 e2' e3
        ,  reduce_fb e2 e2'
        -> reduce_fb (IfE e1 e2 e3) (IfE e1 e2' e3)
    | c_if3_fb
        : forall e1 e2 e3 e3'
        ,  reduce_fb e3 e3'
        -> reduce_fb (IfE e1 e2 e3) (IfE e1 e2 e3')
    .
(* TODO: do we want to add hints about using these as intro rules? *)

Fixpoint val (e:exp) : Prop :=
    match e with
    | Const _   => True
    | LambdaE _ => True
    | _         => False
    end.


(* notation was (infix "\<longmapsto>" 70) in Isabelle/HOL *)
Inductive reduce_bv : exp -> exp -> Prop :=
    | beta_bv
        : forall v e
        ,  val v
        -> reduce_bv (AppE (LambdaE e) v) (∆∆v·e)
    | c_app1_bv
        : forall e1 e1' e2
        ,  reduce_bv e1 e1'
        -> reduce_bv (AppE e1 e2) (AppE e1' e2)
    | c_app2_bv
        : forall v e2 e2'
        ,  val v
        -> reduce_bv e2 e2'
        -> reduce_bv (AppE v e2) (AppE v e2')
    | r_prim_bv
        : forall p c c'
        ,  eval_prim p c = Result c'
        -> reduce_bv (Prim p (Const c)) (Const c')
    | c_prim_bv
        : forall p e e'
        ,  reduce_bv e e'
        -> reduce_bv (Prim p e) (Prim p e')
    | r_if_true_bv
        : forall e2 e3
        , reduce_bv (IfE (Const (BoolC true)) e2 e3) e2
    | r_if_false_bv
        : forall e2 e3
        , reduce_bv (IfE (Const (BoolC false)) e2 e3) e3
    | c_if_bv
        : forall e1 e1' e2 e3
        ,  reduce_bv e1 e1'
        -> reduce_bv (IfE e1 e2 e3) (IfE e1' e2 e3)
    .
(* TODO: do we want to add hints about using these as intro rules? *)

(* notation was (infix "\<longmapsto>*" 70) *)
Definition reduces_bv := RTC_opt reduce_bv.


(* notation was (infix "\<longmapsto>bn" 70) *)
Inductive reduce_bn : exp -> exp -> Prop :=
    | beta_bn
        : forall e e'
        , reduce_bn (AppE (LambdaE e) e') (∆∆e'·e)
    | c_app_bn
        : forall e1 e1' e2
        ,  reduce_bn e1 e1'
        -> reduce_bn (AppE e1 e2) (AppE e1' e2)
    | r_prim_bn
        : forall p c c'
        ,  eval_prim p c = Result c'
        -> reduce_bn (Prim p (Const c)) (Const c')
    | c_prim_bn
        : forall p e e'
        ,  reduce_bn e e'
        -> reduce_bn (Prim p e) (Prim p e')
    | r_if_true_bn
        : forall e2 e3
        , reduce_bn (IfE (Const (BoolC true)) e2 e3) e2
    | r_if_false_bn
        : forall e2 e3
        , reduce_bn (IfE (Const (BoolC false)) e2 e3) e3
    | c_if_bn
        : forall e1 e1' e2 e3
        ,  reduce_bn e1 e1'
        -> reduce_bn (IfE e1 e2 e3) (IfE e1' e2 e3)
    .

End Reduction_Semantics.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section Type_System.
Open Scope exp_scope. (* need to reopen since the old section was closed *)

(* notation for [FunT] was (infix "\<rightarrow>" 75) *)
Inductive ty := 
    | IntT  : ty
    | BoolT : ty
    | FunT  : ty -> ty -> ty
    .

(* Personally, I'd return [FunT t1 t2] everywhere instead of [(t1,t2)]... *)
Definition prim_type (p:primitive) : ty * ty :=
    match p with
    | Inc    => (IntT,  IntT)
    | Dec    => (IntT,  IntT)
    | Neg    => (IntT,  IntT)
    | IsZero => (IntT,  BoolT)
    | Not    => (BoolT, BoolT)
    end.

Definition const_type (c:const) : ty :=
    match c with
    | IntC  _ => IntT
    | BoolC _ => BoolT
    end.


(* See LNVarMap.v for the definitions of [lookup], [lookup_app], [lookup_app_none], [not_dom_lookup_none], [lookup_dom] *)

Definition ty_env := VarMap Var ty.
Implicit Type Γ : ty_env.


Inductive wt : ty_env -> exp -> ty -> Prop :=
    | wt_c
        : forall Γ c T
        ,  const_type c = T
        -> wt Γ (Const c) T
    | wt_p
        : forall Γ p e T1 T2
        ,  wt Γ e T1
        -> prim_type p = (T1, T2)
        -> wt Γ (Prim p e) T2
    | wt_i
        : forall Γ e1 e2 e3 T
        ,  wt Γ e1 BoolT
        -> wt Γ e2 T
        -> wt Γ e3 T
        -> wt Γ (IfE e1 e2 e3) T
    | wt_v
        : forall Γ x T
        ,  lookup x Γ = Some T
        -> wt Γ (FVar x) T
    | wt_l
        : forall Γ e x T1 T2
        ,  x \freshin e
        -> wt ((x,T1)::Γ) (∆x·e) T2
        -> wt Γ (LambdaE e) (FunT T1 T2)
    | wt_a
        : forall Γ e1 e2 T T'
        ,  wt Γ e1 (FunT T T')
        -> wt Γ e2 T
        -> wt Γ (AppE e1 e2) T'
    .


Inductive well_typed : ty_env -> exp -> ty -> Prop :=
    | wt_const
        : forall Γ c T
        ,  const_type c = T
        -> well_typed Γ (Const c) T
    | wt_prim
        : forall Γ p e T1 T2
        ,  well_typed Γ e T1
        -> prim_type p = (T1, T2)
        -> well_typed Γ (Prim p e) T2
    | wt_if
        : forall Γ e1 e2 e3 T
        ,  well_typed Γ e1 BoolT
        -> well_typed Γ e2 T
        -> well_typed Γ e3 T
        -> well_typed Γ (IfE e1 e2 e3) T
    | wt_var
        : forall Γ x T
        ,  lookup x Γ = Some T
        -> well_typed Γ (FVar x) T
    | wt_lambda
        : forall Γ e L T1 T2
        ,  (forall x, x \notin L -> well_typed ((x,T1)::Γ) (∆x·e) T2)
        -> well_typed Γ (LambdaE e) (FunT T1 T2)
    | wt_app
        : forall Γ e1 e2 T T'
        ,  well_typed Γ e1 (FunT T T')
        -> well_typed Γ e2 T
        -> well_typed Γ (AppE e1 e2) T'
    .


Definition wt_env : ty_env -> env -> Prop
    := pointwise (well_typed nil).

End Type_System.

(* Technically we should be using [⊦] instead of [⊢] *)

(* Notation was ("_ \<turnstile>o _ : _" [60,60,60] 59) *)
Notation "Γ ⊢o e : T" := (wt Γ e T)
    (at level 0, e at level 99, no associativity) :type_scope.
(* Notation was ("_ \<turnstile> _ : _" [60,60,60] 59) *)
Notation "Γ ⊢ e : T" := (well_typed Γ e T)
    (at level 0, e at level 99, no associativity) :type_scope.
(* Notation was ("_ \<turnstile> _ " [60,60] 59) *)
Notation "Γ ⊢g ρ" := (wt_env Γ ρ)
    (at level 0, no associativity) :type_scope.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section Properties_of_Substitution.
Open Scope exp_scope. (* need to reopen since the old section was closed *)

(*
lemma bsubst_cross[rule_format]:
  "\<forall> (i::nat) j u v. i \<noteq> j \<and> {i\<rightarrow>u}({j\<rightarrow>v}t) = {j\<rightarrow>v}t \<longrightarrow> {i\<rightarrow>u}t = t"
  apply (induction t)
  apply force
  apply clarify apply (erule_tac x=i in allE) apply (erule_tac x=j in allE) 
    apply force
  apply clarify apply (erule_tac x=i in allE) apply (erule_tac x=i in allE) 
    apply (erule_tac x=i in allE) apply (erule_tac x=j in allE) 
    apply (erule_tac x=j in allE) apply (erule_tac x=j in allE) apply force
  apply force
  apply force
  apply clarify apply (erule_tac x="Suc i" in allE) 
    apply (erule_tac x="Suc j" in allE) apply force
  apply clarify apply (erule_tac x=i in allE) apply (erule_tac x=i in allE) 
    apply force
  done


lemma bsubst_id: fixes e::exp assumes wte: "Γ ⊢ e : T" shows "{k\<rightarrow>e'}e = e"
  using wte apply (induction Γ e T arbitrary: k e')
  apply force apply force apply force apply force defer apply force
  apply (erule_tac x="Suc (list_max L)" in allE) apply (erule impE) 
  apply (rule list_max_fresh) apply simp apply simp apply clarify 
  apply (rule bsubst_cross) apply blast
  done


lemma fv_bsubst: fixes e::exp and e'::exp shows "set (FV e) \<subseteq> set (FV ({k\<rightarrow>e'}e))"
  by (induction e arbitrary: e' k) force+ (* this is a tad slow *)


lemma subst_permute:
  fixes x::nat and z::nat and e::exp and e'::exp
  assumes xz: "z \<notin> set (FV v)" and wte: "Γ ⊢ e' : T"
  shows "{j\<rightarrow>v}([[z~>e']]e) = [[z~>e']]({j\<rightarrow>v}e)"
  using xz wte apply (induction e arbitrary: j x z Γ T e') 
  apply force apply force apply force
  using bsubst_id apply force apply simp
  using subst_id apply force apply force apply force 
  done


lemma decompose_subst[rule_format]:
  "\<forall> u x i. x \<notin> set (FV e) \<longrightarrow> {i\<rightarrow>u}e = [[x~>u]]({i\<rightarrow>FVar x}e)"
  apply (induction e)
  apply force
  apply clarify apply (erule_tac x=u in allE) apply (erule_tac x=x in allE) 
    apply force
  apply force apply force apply force
  apply clarify apply (erule_tac x=u in allE) apply (erule_tac x=x in allE) 
    apply force
  apply force
  done


section "Properties of Multiple Substitutions"


lemma msubst_const[simp]: "[ρ]Const c = Const c" by (induction ρ) auto

lemma msubst_prim[simp]: "[ρ]Prim p e = Prim p ([ρ]e)"
  by (induction ρ arbitrary: p e) auto

lemma msubst_var1: fixes v::exp assumes lx: "lookup x ρ = Some v" and fv: "FV v = []" 
  shows "[ρ]FVar x = v"
  using lx fv apply (induction ρ arbitrary: x v)
  apply force
  apply (case_tac a) apply simp apply (case_tac "x = aa")
  apply simp apply (rule msubst_id) apply auto
  done
  
lemma msubst_var2:
  fixes v::exp assumes lx: "lookup x ρ = None" shows "[ρ]FVar x = FVar x"
  using lx by (induction ρ arbitrary: x v) auto

lemma msubst_if[simp]: "[ρ]IfE e1 e2 e3 = IfE ([ρ]e1) ([ρ]e2) ([ρ]e3)"
  by (induction ρ arbitrary: e1 e2 e3) auto 

lemma msubst_app[simp]: "[ρ]AppE e1 e2 = AppE ([ρ]e1) ([ρ]e2)"
  by (induction ρ arbitrary: e1 e2) auto

lemma msubst_lam[simp]: "[ρ]LambdaE e = LambdaE ([ρ]e)"
  by (induction ρ arbitrary: e) auto

lemma msubst_permute:
  fixes e::exp and ρ::env
  assumes rv: "assoc_dom ρ \<inter> set (FV v) = {}" and wtr: "Γ ⊢ ρ"
  shows "{j\<rightarrow>v}([ρ]e) = [ρ]({j\<rightarrow>v}e)"
using rv wtr proof (induction ρ arbitrary: j v e Γ)
  case (Nil j v e)
  show "{j\<rightarrow>v}[[]] e = [[]]({j\<rightarrow>v}e)" by simp
next
  case (Cons a ρ j v e)
  show "{j\<rightarrow>v}[(a :: ρ)] e = [(a :: ρ)] ({j\<rightarrow>v}e)"
  proof (cases a)
    fix z e' assume a: "a = (z,e')"
    let ?E = "[[z~>e']]e"
    from a have "[(a :: ρ)] e = [ρ]( ?E )" by simp
    from Cons have d: "assoc_dom ρ \<inter> set (FV v) = {}" by auto
    from Cons a obtain Γ' T where g: "Γ = (z,T)::Γ'" and gr2: "Γ' ⊢ ρ" 
      and wtep: "[] ⊢ e' : T" by blast
    from Cons a have zfv: "z \<notin> set (FV v)" by simp
    from Cons a d gr2 have IH: "{j\<rightarrow>v}[ρ] ?E = [ρ]({j\<rightarrow>v} ?E)" by blast
    also with zfv wtep have "... = [ρ]([[z~>e']]({j\<rightarrow>v}e))"
      using subst_permute[of z v "[]" e' T j e] by simp
    finally have "{j\<rightarrow>v}[ρ] ([[z~>e']]e) = [ρ]([[z~>e']]({j\<rightarrow>v}e))" by simp
    with a show ?thesis by simp
  qed
qed


section "Properties of Environments"

lemma wt_env_lookup:
  assumes lg: "lookup x Γ = Some T" and wt_env: "Γ ⊢ ρ"
  shows "\<exists> (v::exp). lookup x ρ = Some v \<and> [] ⊢ v : T"
  using wt_env lg by (induction Γ ρ arbitrary: x T) auto

abbreviation subseteq :: "ty_env => ty_env => bool" (infixl "\<preceq>" 80) where
  "Γ \<preceq> Γ' \<equiv> \<forall> x T. lookup x Γ = Some T \<longrightarrow> lookup x Γ' = Some T"

lemma env_weakening[rule_format]:
  fixes e::exp shows "Γ ⊢ e : T ==> \<forall> Γ'. Γ \<preceq> Γ' \<longrightarrow> Γ' ⊢ e : T" 
  apply (induct rule: well_typed.induct)
  apply force
  apply (rule allI) apply (rule impI) apply (erule_tac x=Γ' in allE) apply force
  apply force
  apply force
  defer
  apply (rule allI) apply (rule impI) apply (erule_tac x=Γ' in allE) 
    apply (erule_tac x=Γ' in allE) apply simp apply blast
  apply (rule allI) apply (rule impI)
  apply (rule wt_lambda) apply (rule allI) apply (rule impI)
  apply (erule_tac x=x in allE) apply (erule impE) apply assumption
  apply auto
done

lemma wt_dom_fv: 
  assumes wt: "Γ ⊢o e : T" shows "set (FV e) \<subseteq> assoc_dom Γ"
  using wt apply (induction Γ e T)
  apply simp
  apply force
  apply force
  using lookup_dom apply force
  defer apply force
  apply auto
  using fv_bsubst apply force
  done

lemma weaken_cons_snoc: assumes xng: "x \<notin> assoc_dom Γ" 
  shows "([(x,T1)]++Γ) \<preceq> (Γ++[(x,T1)])" using xng
proof clarify
  fix x' T assume lxg1: "lookup x' ([(x,T1)]++Γ) = Some T"
  show "lookup x' (Γ++[(x,T1)]) = Some T"
  proof (cases "x' = x")
    assume x: "x' = x"
    with lxg1 have lxg1b: "lookup x' ([(x,T1)]++Γ) = Some T1" by simp
    from xng not_dom_lookup_none have xg: "lookup x Γ = None" by simp
    from lxg1b xg x have "lookup x' (Γ++[(x,T1)]) = Some T1"
      using lookup_app_none[of x Γ] by simp
    with x lxg1 show ?thesis by simp
  next
    assume x: "x' \<noteq> x"
    from x lxg1 have lxg1b: "lookup x' Γ = Some T" by simp
    thus ?thesis by (rule lookup_app)
  qed
qed

section "Substitution Preserves Types"

abbreviation remove_bind :: "var => ty_env => ty_env => bool" where
  "remove_bind z Γ Γ' \<equiv> \<forall>x T. x\<noteq>z \<and> lookup x Γ = Some T 
            \<longrightarrow> lookup x Γ' = Some T"

lemma subst_pres_types:
  fixes M::exp and v::exp and Γ::ty_env
  assumes wtm: "Γ ⊢ M : A" and lx: "lookup x Γ = Some B"
  and rg: "remove_bind x Γ Γ'" and vb: "Γ' ⊢ v : B"
  shows "Γ' ⊢ [[x~>v]]M : A" using wtm lx rg vb
proof (induction arbitrary: x B Γ' v rule: well_typed.induct)
  case (wt_const c T Γ x B Γ' v)
  thus "Γ' ⊢ [[x~>v]](Const c) : T" by auto
next
  case (wt_prim Γ e T1 p T2 x B Γ' v)
  hence "Γ' ⊢ [[x~>v]]e : T1" and "prim_type p = (T1,T2)" by auto
  thus "Γ' ⊢ [[x~>v]] (Prim p e) : T2" by auto
next
  case (wt_if Γ e1 e2 T e3 x B Γ' v)
  from wt_if have wte1: "Γ' ⊢ [[x~>v]]e1 : BoolT" 
    and wte2: "Γ' ⊢ [[x~>v]]e2 : T"  and wte3: "Γ' ⊢ [[x~>v]]e3 : T" by auto
  from wte1 wte2 wte3 show "Γ' ⊢ [[x~>v]] IfE e1 e2 e3 : T" by auto
next
  case (wt_var y Γ T x B Γ' v)
  from wt_var have wtv: "Γ' ⊢ v : B" and ly: "lookup y Γ = Some T" 
      and lx: "lookup x Γ = Some B" and rb: "remove_bind x Γ Γ'" by auto
  show "Γ' ⊢ [[x~>v]]FVar y : T"
  proof (cases "x = y")
    assume x: "x = y"
    have "[] \<preceq> Γ'" by auto
    from wtv x ly lx show ?thesis by simp
  next
    assume x: "x \<noteq> y" with ly rb have "Γ' ⊢ FVar y : T" by auto
    with x show ?thesis by auto
  qed
next
  case (wt_lambda L T1 Γ e T2 x B Γ' v)
  from wt_lambda have lx: "lookup x Γ = Some B" by simp
  from wt_lambda have rb: "remove_bind x Γ Γ'" by simp
  from wt_lambda have wtv: "Γ' ⊢ v : B" by simp
  have "Γ' ⊢ LambdaE ([[x~>v]]e) : T1 \<rightarrow> T2"
  proof clarify
    fix x' assume xL: "x' \<notin> set ((x::L) ++ (map fst Γ'))"
    from wt_lambda xL have "(x',T1)::Γ ⊢ bsubst 0 (FVar x') e : T2" by auto
    from xL lx have lx2: "lookup x ((x',T1)::Γ) = Some B" by simp
    from rb xL have rb2: "remove_bind x ((x',T1)::Γ) ((x',T1)::Γ')" by auto
    from xL have xL2: "x' \<notin> set L" by auto
    from xL have xx: "x' \<noteq> x" by simp
    from xL have xgp: "lookup x' Γ' = None" using not_dom_lookup_none by auto
    from xgp have "Γ' \<preceq> ((x',T1)::Γ')" by simp
    with wtv env_weakening[of Γ' v B "(x',T1)::Γ'"] 
    have wtv2: "(x',T1)::Γ' ⊢ v : B" by blast 
    from wt_lambda lx2 rb2 xL2 wtv2 xx
    have 1: "(x',T1)::Γ' ⊢ [[x~>v]](∆x'·e) : T2" by auto
    from wtv xx  subst_permute
    have "[[x~>v]](∆x'·e) = ∆x'·([[x~>v]]e)" by auto
    with 1 show "(x',T1)::Γ' ⊢ (∆x'·([[x~>v]]e)) : T2" by simp
  qed
  thus "Γ' ⊢ [[x~>v]]LambdaE e : T1 \<rightarrow> T2" by simp
next
  case (wt_app Γ e1 T T' e2 x B Γ' v)
  thus "Γ' ⊢ [[x~>v]]AppE e1 e2 : T'" by auto 
qed

lemma substitution_preserves_types:
  fixes M::exp and v::exp
  assumes wtm: "(x,B)::Γ ⊢ M : A" and vb: "Γ ⊢ v : B"
  shows "Γ ⊢ [[x~>v]]M : A" 
  using wtm vb subst_pres_types[of "(x,B)::Γ" M A x B Γ v] by auto

lemma msubst_preserves_types:
  fixes M::exp and ρ::env assumes wtm: "Γ1++Γ2 ⊢ M : A" and sr: "Γ1 ⊢ ρ"
  shows "Γ2 ⊢ [ρ]M : A" using wtm sr
proof (induction ρ arbitrary: Γ1 Γ2 M A)
  case (Nil Γ1 Γ2 M A) thus "Γ2 ⊢ [[]] M : A" by auto
next
  case (Cons a ρ Γ1 Γ2 M A)
  show "Γ2 ⊢ [(a::ρ)] M : A"
  proof (cases a)
    fix x v assume a: "a = (x,v)"
    from a have 1: "[(a::ρ)]M = [ρ] ([[x~>v]] M)" by simp
    from Cons a obtain Γ1'::ty_env and B::ty where g1: "Γ1 = (x,B)::Γ1'" 
      and wtv: "[] ⊢ v : B" and g1pr: "Γ1' ⊢ ρ" by auto
    from Cons g1 have wtm: "(x,B)::(Γ1'++Γ2) ⊢ M : A" by simp
    from wtv env_weakening[of "[]"]  have wtv2: "Γ1'++Γ2 ⊢ v : B" by auto
    from wtm wtv2 have wtm2: "Γ1'++Γ2 ⊢ [[x~>v]]M : A"
      using substitution_preserves_types by blast
    from wtm2 Cons g1pr have "Γ2 ⊢ [ρ]([[x~>v]]M) : A" by blast
    with a show ?thesis by simp
  qed
qed


section "Adequacy of Locally Nameless Type System"

lemma adequacy1: fixes e::exp assumes wte: "Γ ⊢ e : T" shows "Γ ⊢o e : T"
using wte apply (induction Γ e T) apply force apply force apply force
apply force defer apply force
proof -
  case (wt_lambda L T1 Γ e T2)
  let ?X = "Suc (max (list_max L) (list_max (FV e)))"
  show "Γ ⊢o LambdaE e : T1 \<rightarrow> T2"
  proof
    show "?X \<notin> set (FV e)" using list_max_fresh[of "FV e" "?X"] by auto
  next
    have "?X \<notin> set L" using list_max_fresh by auto
    with wt_lambda show "(?X,T1)::Γ ⊢o (∆?X·e) : T2" by blast
  qed
qed

lemma adequacy2: fixes e::exp assumes wte: "Γ ⊢o e : T" shows "Γ ⊢ e : T"
using wte apply (induction Γ e T rule: wt.induct) apply force 
apply force apply force apply force defer apply force
proof -
  case (wt_l x e T1 Γ T2)
  from wt_l have xfv: "x \<notin> set (FV e)" and
    1: "(x,T1)::Γ ⊢ (∆x·e) : T2" by auto
  show "Γ ⊢ LambdaE e : T1 \<rightarrow> T2"
  proof clarify
    fix x' assume xL: "x' \<notin> set (FV e ++ map fst Γ)"
    from xL not_dom_lookup_none[of x' Γ] 
    have lxg: "lookup x' Γ = None" by simp
    hence rb: "remove_bind x ((x,T1)::Γ) ((x',T1)::Γ)" by auto 
    have lxg2: "lookup x ((x,T1)::Γ) = Some T1" by simp
    have wtxp: "(x',T1)::Γ ⊢ FVar x' : T1" by auto
    from 1 lxg2 rb wtxp subst_pres_types
    have 2: "(x',T1)::Γ ⊢ [[x~>FVar x']](∆x·e) : T2" by blast
    from xfv have 3: "∆x'·e = [[x~>FVar x']](∆x·e)"
      using decompose_subst[of x e] by blast
    from 2 3 show "(x',T1)::Γ ⊢ (∆x'·e) : T2" by simp
  qed
qed


section "Termination via a Logical Relations Proof"

subsection "The Logical Predicates"


fun WTE :: "ty => exp set" and WTV :: "ty => exp set" where
  "WTE T = { e. \<exists> n v. interp e n = Res v \<and> v \<in> WTV T }" |

  "WTV IntT = { v. \<exists> i. v = Const (IntC i) }" |
  "WTV BoolT = {v. \<exists> b. v = Const (BoolC b) }" |
  "WTV (T1\<rightarrow>T2) = {f. \<exists> e. f = LambdaE e \<and> [] ⊢o f : T1 \<rightarrow> T2
     \<and> (\<forall>v\<in>WTV T1.\<exists> n v'. interp (∆∆v·e) n = Res v' \<and> v'\<in>WTV T2)}"


lemma WTE_intro[intro]: 
  assumes ie: "interp e n = Res v" and vt: "v \<in> WTV T"
  shows "e \<in> WTE T" using ie vt by auto


fun WTENV :: "ty_env => env set" where
  "WTENV [] = { [] }" |
  "WTENV ((x,T)::Γ) = {ρ. \<exists> v ρ'. ρ=(x,v)::ρ' 
                          \<and> v \<in> WTV T \<and> ρ' \<in> WTENV Γ }"

subsection "Properties of WTV and WTE"

lemma WTV_implies_WTE:
  assumes wtv: "v \<in> WTV T" shows "v \<in> WTE T"
  using wtv apply (cases T) apply auto by (rule_tac x="Suc 0" in exI, force)+

lemma WTV_implies_WT: assumes wtv: "v \<in> WTV T" shows "[] ⊢o v : T"
  using wtv by (cases T) auto

lemma wtenv_lookup: 
  assumes lg: "lookup x Γ = Some T" and wtenv: "ρ \<in> WTENV Γ" 
  shows "\<exists> v. lookup x ρ = Some v \<and> v \<in> WTV T"
  using lg wtenv by (induction Γ arbitrary: x ρ) auto


subsection "The Main Lemma and Theorem"

lemma prim_type_safe:
  assumes pt: "prim_type p = (T1,T2)" and wt: "const_type c = T1"
  shows "\<exists> c'. eval_prim p c = Result c' \<and> const_type c' = T2"
  using pt wt apply (case_tac p) apply (case_tac c, auto)+ done


lemma wt_dom_fv2: fixes v::exp and T::ty 
  assumes wt: "[] ⊢ v : T" shows "FV v = []"
  using wt wt_dom_fv[of "[]" v T] adequacy1[of "[]" v T] by auto


lemma WT_implies_WTE: fixes e::exp
  assumes wt: "Γ ⊢ e : T" and wtenv: "ρ \<in> WTENV Γ" and wt_env: "Γ ⊢ ρ"
  shows "[ρ]e \<in> WTE T"
using wt wtenv wt_env
proof (induction Γ e T arbitrary: ρ)
  case (wt_const c T Γ ρ)
  from this show "[ρ]Const c \<in> WTE T" 
    apply (case_tac c, auto) apply (rule_tac x="Suc 0" in exI, force)+ done
next
  case (wt_prim Γ e T1 p T2 ρ)
  from wt_prim have "[ρ]e \<in> WTE T1" by auto
  from this obtain v n where 
    ie: "interp ([ρ]e) n = Res v" and wtv: "v \<in> WTV T1" by auto
  from wt_prim have pt: "prim_type p = (T1,T2)" by blast
  from pt wtv obtain c where v: "v = Const c" and ct: "const_type c = T1"
    by (case_tac p) auto
  from pt v ct obtain c' where ip: "eval_prim p c = Result c'"
    and ctp: "const_type c' = T2" using prim_type_safe by blast
  from ie ip ctp v show "[ρ]Prim p e \<in> WTE T2"
    apply (case_tac c', auto) apply (rule_tac x="Suc n" in exI, force)+ done
next
  case (wt_if Γ e1 e2 T e3 ρ)
  from wt_if have "[ρ]e1 \<in> WTE BoolT" by auto
  from this obtain v1 n1 where 
    ie1: "interp ([ρ]e1) n1 = Res v1" and wtv1: "v1 \<in> WTV BoolT" by auto
  from wtv1 obtain b where v1: "v1 = Const (BoolC b)" by auto
  show "[ρ]IfE e1 e2 e3 \<in> WTE T"
  proof (cases b)
    case True
    from wt_if have "[ρ]e2 \<in> WTE T" by auto
    from this obtain v2 n2 where 
      ie2: "interp ([ρ]e2) n2 = Res v2" and wtv2: "v2 \<in> WTV T" by auto
    show ?thesis
    proof (cases "n1 <= n2")
      assume "n1 <= n2"
      with ie1 interp_mono have "interp ([ρ]e1) n2 = Res v1" by blast
      with ie2 True v1 have "interp ([ρ]IfE e1 e2 e3) (Suc n2) = Res v2" by simp
      with wtv2 show ?thesis by blast
    next
      assume "~(n1 <= n2)" -- "This case is the mirror image of the above case"

(*<*)
      from this have n12: "n2 <= n1" by simp
      from ie2 n12 interp_mono have ie2b: "interp ([ρ]e2) n1 = Res v2"  by blast
      from ie1 ie2b True v1
      have iif: "interp ([ρ]IfE e1 e2 e3) (Suc n1) = Res v2" by simp
      from iif wtv2 show ?thesis by blast
(*>*)
    qed
  next
    case False -- "This case is the mirror image of the case for True"

(*<*)
    from wt_if have "[ρ]e3 \<in> WTE T" by auto
    from this obtain v2 n2 where 
      ie2: "interp ([ρ]e3) n2 = Res v2" and wtv2: "v2 \<in> WTV T" by auto
    show ?thesis
    proof (cases "n1 <= n2")
      assume n12: "n1 <= n2"
      from ie1 n12 interp_mono have ie1b: "interp ([ρ]e1) n2 = Res v1"  by blast
      from ie1b ie2 False v1
      have iif: "interp ([ρ]IfE e1 e2 e3) (Suc n2) = Res v2" by simp
      from iif wtv2 show ?thesis by blast
    next
      assume "~(n1 <= n2)"
      from this have n12: "n2 <= n1" by simp
      from ie2 n12 interp_mono have ie2b: "interp ([ρ]e3) n1 = Res v2" by blast
      from ie1 ie2b False v1
      have iif: "interp ([ρ]IfE e1 e2 e3) (Suc n1) = Res v2" by simp
      from iif wtv2 show ?thesis by blast
    qed
(*>*)
  qed
next
  case (wt_var x Γ T ρ)
  from this wtenv_lookup obtain v where lx: "lookup x ρ = Some v" 
    and vt: "v \<in> WTV T" by blast
  from wt_var lx wt_env_lookup[of x Γ T ρ]  have wtv: "[] ⊢ v : T" by auto
  from lx wtv have "[ρ]FVar x = v" using msubst_var1 wt_dom_fv2 by simp
  with vt have "[ρ] FVar x \<in> WTV T" by simp
  with WTV_implies_WTE show "[ρ] FVar x \<in> WTE T" by auto
next
  case (wt_lambda L T1 Γ e T2 ρ)
  from wt_lambda have gr: "Γ ⊢ ρ" by simp
  from wt_lambda have wtr: "ρ \<in> WTENV Γ" by simp
  let ?L = "L ++ (FV e) ++ (FV ([ρ]e)) ++ (map fst Γ) ++ (map fst ρ)"
  have "[] ⊢ LambdaE ([ρ]e) : T1 \<rightarrow> T2" 
  proof
    show "\<forall>x. x \<notin> set ?L \<longrightarrow> [(x, T1)] ⊢ (∆x·[ρ]e) : T2" 
    proof clarify
      fix x assume xl2: "x \<notin> set ?L"
      let ?G1 = "[(x,T1)]++Γ" and ?G2 = "Γ++[(x,T1)]"
      from xl2 wt_lambda have 3: "?G1 ⊢ (∆x·e) : T2" by auto
      from xl2 have 4: "?G1 \<preceq> ?G2" using weaken_cons_snoc by auto
      from 3 4 have "?G2 ⊢ (∆x·e) : T2" using env_weakening by blast
      with gr have 5: "[(x,T1)] ⊢ [ρ](∆x·e) : T2" 
        using msubst_preserves_types by blast
      from xl2 have "assoc_dom ρ \<inter> set (FV (FVar x)) = {}" by simp
      with 5 gr msubst_permute 
      show "[(x,T1)] ⊢ (∆x·([ρ]e)) : T2" by simp
    qed  
  qed
  hence wtlam: "[] ⊢o LambdaE ([ρ]e) : T1 \<rightarrow> T2" by (rule adequacy1)
  have ibody: "\<forall>v\<in>WTV T1.\<exists>n v'. interp(∆∆v·[ρ]e) n=Res v' \<and> v'\<in>WTV T2"
  proof
    fix v assume vt1: "v \<in> WTV T1"
    let ?X = "Suc (list_max [list_max L, list_max (FV e), list_max (FV ([ρ]e)), 
                           list_max (map fst Γ), list_max (map fst ρ)])"
    have xfv: "?X \<notin> set (FV e)" and xl: "?X \<notin> set L" 
      using list_max_fresh by auto
    from vt1 wtr have wtr2: "(?X,v)::ρ \<in> WTENV ((?X,T1)::Γ)" by simp
    from vt1 WTV_implies_WT adequacy2 have "[] ⊢ v : T1" by blast
    with gr have gr2: "((?X,T1)::Γ) ⊢ (?X,v)::ρ" by blast
    let ?E = "[((?X,v)::ρ)](∆?X·e)"
    from wt_lambda xl wtr2 gr2 have IH: "?E \<in> WTE T2" by blast
    from IH obtain v' n where ie: "interp ?E n = Res v'" and 
      wtvp: "v' \<in> WTV T2" by auto
    from vt1 have "FV v = []" 
      using WTV_implies_WT[of v T1] wt_dom_fv[of "[]" v T1] by simp
    hence drfv: "assoc_dom ρ \<inter> set (FV v) = {}" by simp
    have "?E = [ρ]([[?X~>v]](∆?X·e))" by simp
    also with xfv have "... = [ρ](∆∆v·e)" 
      using decompose_subst[of "?X" e 0 v] by simp
    finally have "?E = ∆∆v·[ρ]e"  
      using drfv gr msubst_permute[of ρ v Γ 0 e] by simp
    with ie wtvp
    show "\<exists> n v'. interp(∆∆v·[ρ]e) n = Res v' \<and> v' \<in> WTV T2" by auto
  qed
  from wtlam ibody have lv: "LambdaE ([ρ]e) \<in> WTV (T1 \<rightarrow> T2)" by simp
  have il: "interp (LambdaE ([ρ]e)) (Suc 0) = Res (LambdaE ([ρ]e))" by simp
  from il lv have "LambdaE ([ρ]e) \<in> WTE (T1 \<rightarrow> T2)" by blast
  thus "[ρ](LambdaE e) \<in> WTE (T1 \<rightarrow> T2)" by simp
next
  case (wt_app Γ e1 T T' e2 ρ)
  from wt_app have "Γ ⊢ e1 : T \<rightarrow> T'" by simp
  from wt_app have IH1: "[ρ]e1 \<in> WTE (T \<rightarrow> T')" by simp
  from wt_app have IH2: "[ρ]e2 \<in> WTE T" by simp
  from IH1 obtain v1 n1 where ie1: "interp ([ρ]e1) n1 = Res v1" 
    and v1t: "v1 \<in> WTV (T\<rightarrow>T')" by force 
  from IH2 obtain v2 n2 where ie2: "interp ([ρ]e2) n2 = Res v2" 
    and v2t: "v2 \<in> WTV T" by (cases T) auto
  from v1t obtain e where v1: "v1 = LambdaE e" and
    app: "\<forall>v\<in>WTV T.\<exists>n v'. interp (∆∆v·e) n =Res v' \<and> v'\<in>WTV T'" by auto
  from v2t app obtain n3 v' where ie3: "interp (∆∆v2·e) n3 = Res v'"
    and vpt: "v' \<in> WTV T'" by auto
  let ?N = "n1 + n2 + n3"
  have n1n: "n1 <= ?N" and n2n: "n2 <= ?N" and n3n: "n3 <= ?N" by auto
  from ie1 n1n ie2 n2n ie3 n3n have ie1b: "interp ([ρ]e1) ?N = Res v1" and
    ie2b: "interp ([ρ]e2) ?N = Res v2" and 
    ie3b: "interp (∆∆v2·e) ?N = Res v'" using interp_mono by blast+
  from ie1b ie2b ie3b v1
  have "interp (AppE ([ρ]e1) ([ρ]e2)) (Suc ?N) = Res v'" by auto
  with vpt have "AppE ([ρ]e1) ([ρ]e2) \<in> WTE T'" by blast
  thus "[ρ]AppE e1 e2 \<in> WTE T'" by simp
qed

theorem WT_implies_iterp:
  fixes e::exp assumes wt: "[] ⊢ e : T"
  shows "\<exists> v n. interp e n = Res v \<and> [] ⊢ v : T"
proof -
  let ?R = "[]" and ?G = "[]"
  have 1: "?R \<in> WTENV []" by auto
  have 2: "[] ⊢ []" by auto
  from wt 1 2 have "[?R]e \<in> WTE T" by (rule WT_implies_WTE)
  hence 3: "e \<in> WTE T" by simp
  from 3 obtain v n where ev: "interp e n = Res v" and
    vt: "v \<in> WTV T" by auto
  from vt have "[] ⊢o v : T" by (rule WTV_implies_WT)
  hence "[] ⊢ v : T" by (rule adequacy2)
  with ev show ?thesis by blast
qed
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
