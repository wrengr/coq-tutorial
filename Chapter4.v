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

Require Import WrengrUtil.CoqExtras.ListSet.
Require Import LNVar.

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


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
Section Dynamic_Semantics_via_an_Interpreter.

(** Substitution for local/bound-vars. Replace [BVar j] by [e] in [f]. *)
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
Notation "{{ j ~> e }} f" := (bsubst j e f)
    (at level 0, i at level 99, right associativity) :exp_scope.


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
Notation "[ x ~> e ] f" := (subst x e f)
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


Definition VarMap A := list (Var * A).
Definition env  := VarMap exp.


(* TODO: notation "[_] _" [72,72]71 *)
Fixpoint msubst (rho : env) (e : exp) : exp :=
    match rho with
    | nil         => e
    | (x,v)::rho' => msubst rho' (subst x v e)
    end.


Definition VarMap_dom : forall {A}, VarMap A -> set Var :=
    fun A =>
        list_rect (fun _ => set Var)
            \{}
            (fun ab _ r => fst ab \a r).

Definition env_dom := VarMap_dom exp.


(* TODO: just return a list? use a notation instead in order to abstract over [eq_A_dec]? *)
Definition assoc_dom
    {A} (eq_A_dec : forall x y:A, {x = y} + {x <> y})
    {B}
    (xs : list (A*B))
    : set A :=
        list_to_set A eq_A_dec
            (list_rect (fun _ => set A)
                nil
                (fun ab _ r => fst ab :: r)
                xs).


Lemma msubst_id :
    forall rho e,
    (forall x, x \notin (env_dom rho \n FV e)) ->
    msubst rho e = e.
Proof.
  intro rho; induction rho; simpl; intros e H.
    reflexivity.
    
    destruct a; simpl in *.
    rewrite IHrho.
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

  
(*
lemma interp_mono: assumes ie: "interp e n = Res v'" and nn: "n \<le> n'" 
  shows "interp e n' = Res v'"
  using ie nn apply (induction e n arbitrary: v' n' rule: interp.induct)
  apply (case_tac n') apply simp apply force
  apply (case_tac n') apply force apply (case_tac "interp e n") apply force 
      apply force apply force
  apply (erule inv_interp_if) apply (case_tac n') apply force
    apply (case_tac b) apply force apply force 
  apply simp
  apply simp
  apply (case_tac n') apply simp apply force 
  apply (erule inv_interp_app) apply (case_tac n') apply force apply force
  apply simp
done


section "Reduction Semantics"

primrec close :: "nat \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp" ("{_\<leftarrow>_}_" [54,54,54] 53) where
  "{j\<leftarrow>x} (Const c) = Const c" |
  "{j\<leftarrow>x} (Prim p e') = Prim p ({j\<leftarrow>x} e')" |
  "{j\<leftarrow>x} (IfE e1 e2 e3) = IfE ({j\<leftarrow>x} e1) ({j\<leftarrow>x} e2) ({j\<leftarrow>x} e3)" |
  "{j\<leftarrow>x} (FVar y) = (if x = y then BVar j else FVar y)" |
  "{j\<leftarrow>x} (BVar k) = BVar k" |
  "{j\<leftarrow>x} (LambdaE e') = LambdaE ({(Suc j)\<leftarrow>x} e')" |
  "{j\<leftarrow>x} (AppE e1 e2) = AppE ({j\<leftarrow>x} e1) ({j\<leftarrow>x} e2)"


inductive reduce_fb :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>fb" 70) where
  full_beta[intro!]: "AppE (LambdaE e) e' \<longmapsto>fb ({0\<rightarrow>e'}e)" |
  c_lambda[intro!]: "\<lbrakk> x \<notin> set (FV e); ({0\<rightarrow>FVar x}e) \<longmapsto>fb e' \<rbrakk>
                     \<Longrightarrow> (LambdaE e) \<longmapsto>fb (LambdaE ({0\<leftarrow>x}e'))" |
  c_app1_fb[intro!]: "\<lbrakk> e1 \<longmapsto>fb e1' \<rbrakk> \<Longrightarrow> AppE e1 e2 \<longmapsto>fb AppE e1' e2" |
  c_app2_fb[intro!]: "\<lbrakk> e2 \<longmapsto>fb e2' \<rbrakk> \<Longrightarrow> AppE e1 e2 \<longmapsto>fb AppE e1 e2'" |
  r_prim_fb[intro!]: "\<lbrakk> eval_prim p c = Result c' \<rbrakk>
                     \<Longrightarrow> Prim p (Const c) \<longmapsto>fb Const c'" |
  c_prim_fb[intro!]: "\<lbrakk> e \<longmapsto>fb e' \<rbrakk> \<Longrightarrow> Prim p e \<longmapsto>fb Prim p e'" |
  r_if_true_fb[intro!]: "IfE (Const (BoolC True)) e2 e3 \<longmapsto>fb e2" |
  r_if_false_fb[intro!]: "IfE (Const (BoolC False)) e2 e3 \<longmapsto>fb e3" |
  c_if1_fb[intro!]: "\<lbrakk> e1 \<longmapsto>fb e1' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto>fb IfE e1' e2 e3" |
  c_if2_fb[intro!]: "\<lbrakk> e2 \<longmapsto>fb e2' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto>fb IfE e1 e2' e3" |
  c_if3_fb[intro!]: "\<lbrakk> e3 \<longmapsto>fb e3' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto>fb IfE e1 e2 e3'" 


fun val :: "exp \<Rightarrow> bool" where
  "val (Const c) = True" |
  "val (LambdaE e) = True" |
  "val _ = False" 

inductive reduce_bv :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>" 70) where
  beta_bv[intro!]: "val v \<Longrightarrow> AppE (LambdaE e) v \<longmapsto> ({0\<rightarrow>v}e)" |
  c_app1_bv[intro!]: "\<lbrakk> e1 \<longmapsto> e1' \<rbrakk> \<Longrightarrow> AppE e1 e2 \<longmapsto> AppE e1' e2" |
  c_app2_bv[intro!]: "\<lbrakk> val v; e2 \<longmapsto> e2' \<rbrakk> \<Longrightarrow> AppE v e2 \<longmapsto> AppE v e2'" |
  r_prim_bv[intro!]: "\<lbrakk> eval_prim p c = Result c' \<rbrakk>
                     \<Longrightarrow> Prim p (Const c) \<longmapsto> Const c'" |
  c_prim_bv[intro!]: "\<lbrakk> e \<longmapsto> e' \<rbrakk> \<Longrightarrow> Prim p e \<longmapsto> Prim p e'" |
  r_if_true_bv[intro!]: "IfE (Const (BoolC True)) e2 e3 \<longmapsto> e2" |
  r_if_false_bv[intro!]: "IfE (Const (BoolC False)) e2 e3 \<longmapsto> e3" |
  c_if_bv[intro!]: "\<lbrakk> e1 \<longmapsto> e1' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto> IfE e1' e2 e3" 

inductive reduces_bv :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>*" 70) where
 red_bv_nil[intro!]: "(e::exp) \<longmapsto>* e" |
 red_bv_cons[intro!]: "\<lbrakk> (e1::exp) \<longmapsto> e2; e2 \<longmapsto>* e3 \<rbrakk> \<Longrightarrow> e1 \<longmapsto>* e3"


inductive reduce_bn :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>bn" 70) where
  beta_bn[intro!]: "AppE (LambdaE e) e' \<longmapsto>bn ({0\<rightarrow>e'}e)" |
  c_app_bn[intro!]: "\<lbrakk> e1 \<longmapsto>bn e1' \<rbrakk> \<Longrightarrow> AppE e1 e2 \<longmapsto>bn AppE e1' e2" |
  r_prim_bn[intro!]: "\<lbrakk> eval_prim p c = Result c' \<rbrakk>
                     \<Longrightarrow> Prim p (Const c) \<longmapsto>bn Const c'" |
  c_prim_bn[intro!]: "\<lbrakk> e \<longmapsto>bn e' \<rbrakk> \<Longrightarrow> Prim p e \<longmapsto>bn Prim p e'" |
  r_if_true_bn[intro!]: "IfE (Const (BoolC True)) e2 e3 \<longmapsto>bn e2" |
  r_if_false_bn[intro!]: "IfE (Const (BoolC False)) e2 e3 \<longmapsto>bn e3" |
  c_if_bn[intro!]: "\<lbrakk> e1 \<longmapsto>bn e1' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto>bn IfE e1' e2 e3"



section "Type System"


datatype ty = IntT | BoolT | FunT ty ty (infix "\<rightarrow>" 75)


primrec prim_type :: "primitive \<Rightarrow> ty \<times> ty" where
   "prim_type Inc = (IntT, IntT)" |
   "prim_type Dec = (IntT, IntT)" |
   "prim_type Neg = (IntT, IntT)" |
   "prim_type IsZero = (IntT, BoolT)" |
   "prim_type Not = (BoolT, BoolT)" 

primrec const_type :: "const \<Rightarrow> ty" where
  "const_type (IntC n) = IntT" |
  "const_type (BoolC b) = BoolT"

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup k [] = None" |
  "lookup k ((k',v)#ls) = (if k = k' then Some v else lookup k ls)"


lemma lookup_app: assumes lx: "lookup x \<Gamma> = Some v" 
  shows "lookup x (\<Gamma>@\<Gamma>') = Some v"
  using lx by (induction \<Gamma> arbitrary: x v) auto 

lemma lookup_app_none: assumes lx: "lookup x \<Gamma> = None" 
  shows "lookup x (\<Gamma>@[(x,T)]) = Some T"
  using lx by (induction \<Gamma> arbitrary: x T) auto

lemma not_dom_lookup_none: 
  assumes x: "x \<notin> assoc_dom \<Gamma>" shows "lookup x \<Gamma> = None"
  using x by (induction \<Gamma> arbitrary: x) auto

lemma lookup_dom: 
  assumes x: "lookup x \<Gamma> = Some T" shows "x \<in> assoc_dom \<Gamma>"
  using x apply (induction \<Gamma> arbitrary: x T) apply auto 
  apply (case_tac "x = a") by auto 

type_synonym ty_env = "(var \<times> ty) list"


inductive wt :: "ty_env \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile>o _ : _" [60,60,60] 59) where
  wt_c[intro!]: "\<lbrakk> const_type c = T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>o Const c : T" |
  wt_p[intro!]: "\<lbrakk> \<Gamma> \<turnstile>o e : T1; prim_type p = (T1, T2) \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>o Prim p e : T2" |
  wt_i[intro!]: "\<lbrakk> \<Gamma> \<turnstile>o e1 : BoolT; \<Gamma> \<turnstile>o e2 : T; \<Gamma> \<turnstile>o e3 : T \<rbrakk> 
                    \<Longrightarrow> \<Gamma> \<turnstile>o IfE e1 e2 e3 : T" |
  wt_v[intro!]: "\<lbrakk> lookup x \<Gamma> = Some T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>o FVar x : T" |
  wt_l[intro!]: "\<lbrakk> x \<notin> set (FV e); (x,T1)#\<Gamma> \<turnstile>o ({0\<rightarrow>FVar x} e) : T2 \<rbrakk> 
          \<Longrightarrow> \<Gamma> \<turnstile>o LambdaE e : T1\<rightarrow>T2" |
  wt_a[intro!]: "\<lbrakk> \<Gamma> \<turnstile>o e1 : T \<rightarrow> T'; \<Gamma> \<turnstile>o e2 : T \<rbrakk> 
          \<Longrightarrow> \<Gamma> \<turnstile>o AppE e1 e2 : T'"


inductive well_typed :: "ty_env \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [60,60,60] 59) where
  wt_const[intro!]: "\<lbrakk> const_type c = T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Const c : T" |
  wt_prim[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e : T1; prim_type p = (T1, T2) \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile> Prim p e : T2" |
  wt_if[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : BoolT; \<Gamma> \<turnstile> e2 : T; \<Gamma> \<turnstile> e3 : T \<rbrakk> 
                    \<Longrightarrow> \<Gamma> \<turnstile> IfE e1 e2 e3 : T" |
  wt_var[intro!]: "\<lbrakk> lookup x \<Gamma> = Some T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> FVar x : T" |
  wt_lambda[intro!]: "\<lbrakk> \<forall> x. x \<notin> set L \<longrightarrow> (x,T1)#\<Gamma> \<turnstile> ({0\<rightarrow>FVar x} e) : T2 \<rbrakk> 
          \<Longrightarrow> \<Gamma> \<turnstile> LambdaE e : T1\<rightarrow>T2" |
  wt_app[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : T \<rightarrow> T'; \<Gamma> \<turnstile> e2 : T \<rbrakk> 
          \<Longrightarrow> \<Gamma> \<turnstile> AppE e1 e2 : T'"

inductive_cases
  inv_wt_fvar[elim!]: "\<Gamma> \<turnstile> FVar x : T" and
  inv_wt_bvar[elim!]: "\<Gamma> \<turnstile> BVar k : T" and
  inv_wt_const[elim!]: "\<Gamma> \<turnstile> Const c : T" and
  inv_wt_prim[elim!]: "\<Gamma> \<turnstile> Prim p e : T" and
  inv_wt_lambda[elim!]: "\<Gamma> \<turnstile> LambdaE e : T" and
  inv_wt_app[elim!]: "\<Gamma> \<turnstile> AppE e1 e2 : T"


inductive wt_env :: "ty_env \<Rightarrow> env \<Rightarrow> bool" ("_ \<turnstile> _" [60,60] 59) where
wt_nil[intro!]: "[] \<turnstile> []" |
wt_cons[intro!]: "\<lbrakk> [] \<turnstile> v : T; \<Gamma> \<turnstile> \<rho> \<rbrakk> \<Longrightarrow> (x,T)#\<Gamma> \<turnstile> (x,v)#\<rho>"

inductive_cases
  inv_wt_nil[elim!]: "\<Gamma> \<turnstile> []" and
  inv_wt_cons[elim!]: "\<Gamma> \<turnstile> (x,v)#\<rho>"


section "Properties of Substitution" 


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


lemma bsubst_id: fixes e::exp assumes wte: "\<Gamma> \<turnstile> e : T" shows "{k\<rightarrow>e'}e = e"
  using wte apply (induction \<Gamma> e T arbitrary: k e')
  apply force apply force apply force apply force defer apply force
  apply (erule_tac x="Suc (list_max L)" in allE) apply (erule impE) 
  apply (rule list_max_fresh) apply simp apply simp apply clarify 
  apply (rule bsubst_cross) apply blast
  done


lemma fv_bsubst: fixes e::exp and e'::exp shows "set (FV e) \<subseteq> set (FV ({k\<rightarrow>e'}e))"
  by (induction e arbitrary: e' k) force+ (* this is a tad slow *)


lemma subst_permute:
  fixes x::nat and z::nat and e::exp and e'::exp
  assumes xz: "z \<notin> set (FV v)" and wte: "\<Gamma> \<turnstile> e' : T"
  shows "{j\<rightarrow>v}([z\<mapsto>e']e) = [z\<mapsto>e']({j\<rightarrow>v}e)"
  using xz wte apply (induction e arbitrary: j x z \<Gamma> T e') 
  apply force apply force apply force
  using bsubst_id apply force apply simp
  using subst_id apply force apply force apply force 
  done


lemma decompose_subst[rule_format]:
  "\<forall> u x i. x \<notin> set (FV e) \<longrightarrow> {i\<rightarrow>u}e = [x\<mapsto>u]({i\<rightarrow>FVar x}e)"
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


lemma msubst_const[simp]: "[\<rho>]Const c = Const c" by (induction \<rho>) auto

lemma msubst_prim[simp]: "[\<rho>]Prim p e = Prim p ([\<rho>]e)"
  by (induction \<rho> arbitrary: p e) auto

lemma msubst_var1: fixes v::exp assumes lx: "lookup x \<rho> = Some v" and fv: "FV v = []" 
  shows "[\<rho>]FVar x = v"
  using lx fv apply (induction \<rho> arbitrary: x v)
  apply force
  apply (case_tac a) apply simp apply (case_tac "x = aa")
  apply simp apply (rule msubst_id) apply auto
  done
  
lemma msubst_var2:
  fixes v::exp assumes lx: "lookup x \<rho> = None" shows "[\<rho>]FVar x = FVar x"
  using lx by (induction \<rho> arbitrary: x v) auto

lemma msubst_if[simp]: "[\<rho>]IfE e1 e2 e3 = IfE ([\<rho>]e1) ([\<rho>]e2) ([\<rho>]e3)"
  by (induction \<rho> arbitrary: e1 e2 e3) auto 

lemma msubst_app[simp]: "[\<rho>]AppE e1 e2 = AppE ([\<rho>]e1) ([\<rho>]e2)"
  by (induction \<rho> arbitrary: e1 e2) auto

lemma msubst_lam[simp]: "[\<rho>]LambdaE e = LambdaE ([\<rho>]e)"
  by (induction \<rho> arbitrary: e) auto

lemma msubst_permute:
  fixes e::exp and \<rho>::env
  assumes rv: "assoc_dom \<rho> \<inter> set (FV v) = {}" and wtr: "\<Gamma> \<turnstile> \<rho>"
  shows "{j\<rightarrow>v}([\<rho>]e) = [\<rho>]({j\<rightarrow>v}e)"
using rv wtr proof (induction \<rho> arbitrary: j v e \<Gamma>)
  case (Nil j v e)
  show "{j\<rightarrow>v}[[]] e = [[]]({j\<rightarrow>v}e)" by simp
next
  case (Cons a \<rho> j v e)
  show "{j\<rightarrow>v}[(a # \<rho>)] e = [(a # \<rho>)] ({j\<rightarrow>v}e)"
  proof (cases a)
    fix z e' assume a: "a = (z,e')"
    let ?E = "[z\<mapsto>e']e"
    from a have "[(a # \<rho>)] e = [\<rho>]( ?E )" by simp
    from Cons have d: "assoc_dom \<rho> \<inter> set (FV v) = {}" by auto
    from Cons a obtain \<Gamma>' T where g: "\<Gamma> = (z,T)#\<Gamma>'" and gr2: "\<Gamma>' \<turnstile> \<rho>" 
      and wtep: "[] \<turnstile> e' : T" by blast
    from Cons a have zfv: "z \<notin> set (FV v)" by simp
    from Cons a d gr2 have IH: "{j\<rightarrow>v}[\<rho>] ?E = [\<rho>]({j\<rightarrow>v} ?E)" by blast
    also with zfv wtep have "... = [\<rho>]([z\<mapsto>e']({j\<rightarrow>v}e))"
      using subst_permute[of z v "[]" e' T j e] by simp
    finally have "{j\<rightarrow>v}[\<rho>] ([z\<mapsto>e']e) = [\<rho>]([z\<mapsto>e']({j\<rightarrow>v}e))" by simp
    with a show ?thesis by simp
  qed
qed


section "Properties of Environments"

lemma wt_env_lookup:
  assumes lg: "lookup x \<Gamma> = Some T" and wt_env: "\<Gamma> \<turnstile> \<rho>"
  shows "\<exists> (v::exp). lookup x \<rho> = Some v \<and> [] \<turnstile> v : T"
  using wt_env lg by (induction \<Gamma> \<rho> arbitrary: x T) auto

abbreviation subseteq :: "ty_env \<Rightarrow> ty_env \<Rightarrow> bool" (infixl "\<preceq>" 80) where
  "\<Gamma> \<preceq> \<Gamma>' \<equiv> \<forall> x T. lookup x \<Gamma> = Some T \<longrightarrow> lookup x \<Gamma>' = Some T"

lemma env_weakening[rule_format]:
  fixes e::exp shows "\<Gamma> \<turnstile> e : T \<Longrightarrow> \<forall> \<Gamma>'. \<Gamma> \<preceq> \<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> e : T" 
  apply (induct rule: well_typed.induct)
  apply force
  apply (rule allI) apply (rule impI) apply (erule_tac x=\<Gamma>' in allE) apply force
  apply force
  apply force
  defer
  apply (rule allI) apply (rule impI) apply (erule_tac x=\<Gamma>' in allE) 
    apply (erule_tac x=\<Gamma>' in allE) apply simp apply blast
  apply (rule allI) apply (rule impI)
  apply (rule wt_lambda) apply (rule allI) apply (rule impI)
  apply (erule_tac x=x in allE) apply (erule impE) apply assumption
  apply auto
done

lemma wt_dom_fv: 
  assumes wt: "\<Gamma> \<turnstile>o e : T" shows "set (FV e) \<subseteq> assoc_dom \<Gamma>"
  using wt apply (induction \<Gamma> e T)
  apply simp
  apply force
  apply force
  using lookup_dom apply force
  defer apply force
  apply auto
  using fv_bsubst apply force
  done

lemma weaken_cons_snoc: assumes xng: "x \<notin> assoc_dom \<Gamma>" 
  shows "([(x,T1)]@\<Gamma>) \<preceq> (\<Gamma>@[(x,T1)])" using xng
proof clarify
  fix x' T assume lxg1: "lookup x' ([(x,T1)]@\<Gamma>) = Some T"
  show "lookup x' (\<Gamma>@[(x,T1)]) = Some T"
  proof (cases "x' = x")
    assume x: "x' = x"
    with lxg1 have lxg1b: "lookup x' ([(x,T1)]@\<Gamma>) = Some T1" by simp
    from xng not_dom_lookup_none have xg: "lookup x \<Gamma> = None" by simp
    from lxg1b xg x have "lookup x' (\<Gamma>@[(x,T1)]) = Some T1"
      using lookup_app_none[of x \<Gamma>] by simp
    with x lxg1 show ?thesis by simp
  next
    assume x: "x' \<noteq> x"
    from x lxg1 have lxg1b: "lookup x' \<Gamma> = Some T" by simp
    thus ?thesis by (rule lookup_app)
  qed
qed

section "Substitution Preserves Types"

abbreviation remove_bind :: "var \<Rightarrow> ty_env \<Rightarrow> ty_env \<Rightarrow> bool" where
  "remove_bind z \<Gamma> \<Gamma>' \<equiv> \<forall>x T. x\<noteq>z \<and> lookup x \<Gamma> = Some T 
            \<longrightarrow> lookup x \<Gamma>' = Some T"

lemma subst_pres_types:
  fixes M::exp and v::exp and \<Gamma>::ty_env
  assumes wtm: "\<Gamma> \<turnstile> M : A" and lx: "lookup x \<Gamma> = Some B"
  and rg: "remove_bind x \<Gamma> \<Gamma>'" and vb: "\<Gamma>' \<turnstile> v : B"
  shows "\<Gamma>' \<turnstile> [x \<mapsto> v]M : A" using wtm lx rg vb
proof (induction arbitrary: x B \<Gamma>' v rule: well_typed.induct)
  case (wt_const c T \<Gamma> x B \<Gamma>' v)
  thus "\<Gamma>' \<turnstile> [x\<mapsto>v](Const c) : T" by auto
next
  case (wt_prim \<Gamma> e T1 p T2 x B \<Gamma>' v)
  hence "\<Gamma>' \<turnstile> [x\<mapsto>v]e : T1" and "prim_type p = (T1,T2)" by auto
  thus "\<Gamma>' \<turnstile> [x\<mapsto>v] (Prim p e) : T2" by auto
next
  case (wt_if \<Gamma> e1 e2 T e3 x B \<Gamma>' v)
  from wt_if have wte1: "\<Gamma>' \<turnstile> [x\<mapsto>v]e1 : BoolT" 
    and wte2: "\<Gamma>' \<turnstile> [x\<mapsto>v]e2 : T"  and wte3: "\<Gamma>' \<turnstile> [x\<mapsto>v]e3 : T" by auto
  from wte1 wte2 wte3 show "\<Gamma>' \<turnstile> [x\<mapsto>v] IfE e1 e2 e3 : T" by auto
next
  case (wt_var y \<Gamma> T x B \<Gamma>' v)
  from wt_var have wtv: "\<Gamma>' \<turnstile> v : B" and ly: "lookup y \<Gamma> = Some T" 
      and lx: "lookup x \<Gamma> = Some B" and rb: "remove_bind x \<Gamma> \<Gamma>'" by auto
  show "\<Gamma>' \<turnstile> [x\<mapsto>v]FVar y : T"
  proof (cases "x = y")
    assume x: "x = y"
    have "[] \<preceq> \<Gamma>'" by auto
    from wtv x ly lx show ?thesis by simp
  next
    assume x: "x \<noteq> y" with ly rb have "\<Gamma>' \<turnstile> FVar y : T" by auto
    with x show ?thesis by auto
  qed
next
  case (wt_lambda L T1 \<Gamma> e T2 x B \<Gamma>' v)
  from wt_lambda have lx: "lookup x \<Gamma> = Some B" by simp
  from wt_lambda have rb: "remove_bind x \<Gamma> \<Gamma>'" by simp
  from wt_lambda have wtv: "\<Gamma>' \<turnstile> v : B" by simp
  have "\<Gamma>' \<turnstile> LambdaE ([x\<mapsto>v]e) : T1 \<rightarrow> T2"
  proof clarify
    fix x' assume xL: "x' \<notin> set ((x#L) @ (map fst \<Gamma>'))"
    from wt_lambda xL have "(x',T1)#\<Gamma> \<turnstile> bsubst 0 (FVar x') e : T2" by auto
    from xL lx have lx2: "lookup x ((x',T1)#\<Gamma>) = Some B" by simp
    from rb xL have rb2: "remove_bind x ((x',T1)#\<Gamma>) ((x',T1)#\<Gamma>')" by auto
    from xL have xL2: "x' \<notin> set L" by auto
    from xL have xx: "x' \<noteq> x" by simp
    from xL have xgp: "lookup x' \<Gamma>' = None" using not_dom_lookup_none by auto
    from xgp have "\<Gamma>' \<preceq> ((x',T1)#\<Gamma>')" by simp
    with wtv env_weakening[of \<Gamma>' v B "(x',T1)#\<Gamma>'"] 
    have wtv2: "(x',T1)#\<Gamma>' \<turnstile> v : B" by blast 
    from wt_lambda lx2 rb2 xL2 wtv2 xx
    have 1: "(x',T1)#\<Gamma>' \<turnstile> [x\<mapsto>v]({0\<rightarrow>FVar x'} e) : T2" by auto
    from wtv xx  subst_permute
    have "[x\<mapsto>v]({0\<rightarrow>FVar x'}e) = {0\<rightarrow>FVar x'}([x\<mapsto>v]e)" by auto
    with 1 show "(x',T1)#\<Gamma>' \<turnstile> ({0\<rightarrow>FVar x'}([x\<mapsto>v]e)) : T2" by simp
  qed
  thus "\<Gamma>' \<turnstile> [x\<mapsto>v]LambdaE e : T1 \<rightarrow> T2" by simp
next
  case (wt_app \<Gamma> e1 T T' e2 x B \<Gamma>' v)
  thus "\<Gamma>' \<turnstile> [x\<mapsto>v]AppE e1 e2 : T'" by auto 
qed

lemma substitution_preserves_types:
  fixes M::exp and v::exp
  assumes wtm: "(x,B)#\<Gamma> \<turnstile> M : A" and vb: "\<Gamma> \<turnstile> v : B"
  shows "\<Gamma> \<turnstile> [x \<mapsto> v]M : A" 
  using wtm vb subst_pres_types[of "(x,B)#\<Gamma>" M A x B \<Gamma> v] by auto

lemma msubst_preserves_types:
  fixes M::exp and \<rho>::env assumes wtm: "\<Gamma>1@\<Gamma>2 \<turnstile> M : A" and sr: "\<Gamma>1 \<turnstile> \<rho>"
  shows "\<Gamma>2 \<turnstile> [\<rho>]M : A" using wtm sr
proof (induction \<rho> arbitrary: \<Gamma>1 \<Gamma>2 M A)
  case (Nil \<Gamma>1 \<Gamma>2 M A) thus "\<Gamma>2 \<turnstile> [[]] M : A" by auto
next
  case (Cons a \<rho> \<Gamma>1 \<Gamma>2 M A)
  show "\<Gamma>2 \<turnstile> [(a#\<rho>)] M : A"
  proof (cases a)
    fix x v assume a: "a = (x,v)"
    from a have 1: "[(a#\<rho>)]M = [\<rho>] ([x\<mapsto>v] M)" by simp
    from Cons a obtain \<Gamma>1'::ty_env and B::ty where g1: "\<Gamma>1 = (x,B)#\<Gamma>1'" 
      and wtv: "[] \<turnstile> v : B" and g1pr: "\<Gamma>1' \<turnstile> \<rho>" by auto
    from Cons g1 have wtm: "(x,B)#(\<Gamma>1'@\<Gamma>2) \<turnstile> M : A" by simp
    from wtv env_weakening[of "[]"]  have wtv2: "\<Gamma>1'@\<Gamma>2 \<turnstile> v : B" by auto
    from wtm wtv2 have wtm2: "\<Gamma>1'@\<Gamma>2 \<turnstile> [x\<mapsto>v]M : A"
      using substitution_preserves_types by blast
    from wtm2 Cons g1pr have "\<Gamma>2 \<turnstile> [\<rho>]([x\<mapsto>v]M) : A" by blast
    with a show ?thesis by simp
  qed
qed


section "Adequacy of Locally Nameless Type System"

lemma adequacy1: fixes e::exp assumes wte: "\<Gamma> \<turnstile> e : T" shows "\<Gamma> \<turnstile>o e : T"
using wte apply (induction \<Gamma> e T) apply force apply force apply force
apply force defer apply force
proof -
  case (wt_lambda L T1 \<Gamma> e T2)
  let ?X = "Suc (max (list_max L) (list_max (FV e)))"
  show "\<Gamma> \<turnstile>o LambdaE e : T1 \<rightarrow> T2"
  proof
    show "?X \<notin> set (FV e)" using list_max_fresh[of "FV e" "?X"] by auto
  next
    have "?X \<notin> set L" using list_max_fresh by auto
    with wt_lambda show "(?X,T1)#\<Gamma> \<turnstile>o ({0\<rightarrow>FVar ?X} e) : T2" by blast
  qed
qed

lemma adequacy2: fixes e::exp assumes wte: "\<Gamma> \<turnstile>o e : T" shows "\<Gamma> \<turnstile> e : T"
using wte apply (induction \<Gamma> e T rule: wt.induct) apply force 
apply force apply force apply force defer apply force
proof -
  case (wt_l x e T1 \<Gamma> T2)
  from wt_l have xfv: "x \<notin> set (FV e)" and
    1: "(x,T1)#\<Gamma> \<turnstile> ({0\<rightarrow>FVar x}e) : T2" by auto
  show "\<Gamma> \<turnstile> LambdaE e : T1 \<rightarrow> T2"
  proof clarify
    fix x' assume xL: "x' \<notin> set (FV e @ map fst \<Gamma>)"
    from xL not_dom_lookup_none[of x' \<Gamma>] 
    have lxg: "lookup x' \<Gamma> = None" by simp
    hence rb: "remove_bind x ((x,T1)#\<Gamma>) ((x',T1)#\<Gamma>)" by auto 
    have lxg2: "lookup x ((x,T1)#\<Gamma>) = Some T1" by simp
    have wtxp: "(x',T1)#\<Gamma> \<turnstile> FVar x' : T1" by auto
    from 1 lxg2 rb wtxp subst_pres_types
    have 2: "(x',T1)#\<Gamma> \<turnstile> [x\<mapsto>FVar x']({0\<rightarrow>FVar x}e) : T2" by blast
    from xfv have 3: "{0\<rightarrow>FVar x'}e = [x\<mapsto>FVar x']({0\<rightarrow>FVar x}e)"
      using decompose_subst[of x e] by blast
    from 2 3 show "(x',T1)#\<Gamma> \<turnstile> ({0\<rightarrow>FVar x'}e) : T2" by simp
  qed
qed


section "Termination via a Logical Relations Proof"

subsection "The Logical Predicates"


fun WTE :: "ty \<Rightarrow> exp set" and WTV :: "ty \<Rightarrow> exp set" where
  "WTE T = { e. \<exists> n v. interp e n = Res v \<and> v \<in> WTV T }" |

  "WTV IntT = { v. \<exists> i. v = Const (IntC i) }" |
  "WTV BoolT = {v. \<exists> b. v = Const (BoolC b) }" |
  "WTV (T1\<rightarrow>T2) = {f. \<exists> e. f = LambdaE e \<and> [] \<turnstile>o f : T1 \<rightarrow> T2
     \<and> (\<forall>v\<in>WTV T1.\<exists> n v'. interp ({0\<rightarrow>v} e) n = Res v' \<and> v'\<in>WTV T2)}"


lemma WTE_intro[intro]: 
  assumes ie: "interp e n = Res v" and vt: "v \<in> WTV T"
  shows "e \<in> WTE T" using ie vt by auto


fun WTENV :: "ty_env \<Rightarrow> env set" where
  "WTENV [] = { [] }" |
  "WTENV ((x,T)#\<Gamma>) = {\<rho>. \<exists> v \<rho>'. \<rho>=(x,v)#\<rho>' 
                          \<and> v \<in> WTV T \<and> \<rho>' \<in> WTENV \<Gamma> }"

subsection "Properties of WTV and WTE"

lemma WTV_implies_WTE:
  assumes wtv: "v \<in> WTV T" shows "v \<in> WTE T"
  using wtv apply (cases T) apply auto by (rule_tac x="Suc 0" in exI, force)+

lemma WTV_implies_WT: assumes wtv: "v \<in> WTV T" shows "[] \<turnstile>o v : T"
  using wtv by (cases T) auto

lemma wtenv_lookup: 
  assumes lg: "lookup x \<Gamma> = Some T" and wtenv: "\<rho> \<in> WTENV \<Gamma>" 
  shows "\<exists> v. lookup x \<rho> = Some v \<and> v \<in> WTV T"
  using lg wtenv by (induction \<Gamma> arbitrary: x \<rho>) auto


subsection "The Main Lemma and Theorem"

lemma prim_type_safe:
  assumes pt: "prim_type p = (T1,T2)" and wt: "const_type c = T1"
  shows "\<exists> c'. eval_prim p c = Result c' \<and> const_type c' = T2"
  using pt wt apply (case_tac p) apply (case_tac c, auto)+ done


lemma wt_dom_fv2: fixes v::exp and T::ty 
  assumes wt: "[] \<turnstile> v : T" shows "FV v = []"
  using wt wt_dom_fv[of "[]" v T] adequacy1[of "[]" v T] by auto


lemma WT_implies_WTE: fixes e::exp
  assumes wt: "\<Gamma> \<turnstile> e : T" and wtenv: "\<rho> \<in> WTENV \<Gamma>" and wt_env: "\<Gamma> \<turnstile> \<rho>"
  shows "[\<rho>]e \<in> WTE T"
using wt wtenv wt_env
proof (induction \<Gamma> e T arbitrary: \<rho>)
  case (wt_const c T \<Gamma> \<rho>)
  from this show "[\<rho>]Const c \<in> WTE T" 
    apply (case_tac c, auto) apply (rule_tac x="Suc 0" in exI, force)+ done
next
  case (wt_prim \<Gamma> e T1 p T2 \<rho>)
  from wt_prim have "[\<rho>]e \<in> WTE T1" by auto
  from this obtain v n where 
    ie: "interp ([\<rho>]e) n = Res v" and wtv: "v \<in> WTV T1" by auto
  from wt_prim have pt: "prim_type p = (T1,T2)" by blast
  from pt wtv obtain c where v: "v = Const c" and ct: "const_type c = T1"
    by (case_tac p) auto
  from pt v ct obtain c' where ip: "eval_prim p c = Result c'"
    and ctp: "const_type c' = T2" using prim_type_safe by blast
  from ie ip ctp v show "[\<rho>]Prim p e \<in> WTE T2"
    apply (case_tac c', auto) apply (rule_tac x="Suc n" in exI, force)+ done
next
  case (wt_if \<Gamma> e1 e2 T e3 \<rho>)
  from wt_if have "[\<rho>]e1 \<in> WTE BoolT" by auto
  from this obtain v1 n1 where 
    ie1: "interp ([\<rho>]e1) n1 = Res v1" and wtv1: "v1 \<in> WTV BoolT" by auto
  from wtv1 obtain b where v1: "v1 = Const (BoolC b)" by auto
  show "[\<rho>]IfE e1 e2 e3 \<in> WTE T"
  proof (cases b)
    case True
    from wt_if have "[\<rho>]e2 \<in> WTE T" by auto
    from this obtain v2 n2 where 
      ie2: "interp ([\<rho>]e2) n2 = Res v2" and wtv2: "v2 \<in> WTV T" by auto
    show ?thesis
    proof (cases "n1 \<le> n2")
      assume "n1 \<le> n2"
      with ie1 interp_mono have "interp ([\<rho>]e1) n2 = Res v1" by blast
      with ie2 True v1 have "interp ([\<rho>]IfE e1 e2 e3) (Suc n2) = Res v2" by simp
      with wtv2 show ?thesis by blast
    next
      assume "\<not> n1 \<le> n2" -- "This case is the mirror image of the above case"

(*<*)
      from this have n12: "n2 \<le> n1" by simp
      from ie2 n12 interp_mono have ie2b: "interp ([\<rho>]e2) n1 = Res v2"  by blast
      from ie1 ie2b True v1
      have iif: "interp ([\<rho>]IfE e1 e2 e3) (Suc n1) = Res v2" by simp
      from iif wtv2 show ?thesis by blast
(*>*)
    qed
  next
    case False -- "This case is the mirror image of the case for True"

(*<*)
    from wt_if have "[\<rho>]e3 \<in> WTE T" by auto
    from this obtain v2 n2 where 
      ie2: "interp ([\<rho>]e3) n2 = Res v2" and wtv2: "v2 \<in> WTV T" by auto
    show ?thesis
    proof (cases "n1 \<le> n2")
      assume n12: "n1 \<le> n2"
      from ie1 n12 interp_mono have ie1b: "interp ([\<rho>]e1) n2 = Res v1"  by blast
      from ie1b ie2 False v1
      have iif: "interp ([\<rho>]IfE e1 e2 e3) (Suc n2) = Res v2" by simp
      from iif wtv2 show ?thesis by blast
    next
      assume "\<not> n1 \<le> n2"
      from this have n12: "n2 \<le> n1" by simp
      from ie2 n12 interp_mono have ie2b: "interp ([\<rho>]e3) n1 = Res v2" by blast
      from ie1 ie2b False v1
      have iif: "interp ([\<rho>]IfE e1 e2 e3) (Suc n1) = Res v2" by simp
      from iif wtv2 show ?thesis by blast
    qed
(*>*)
  qed
next
  case (wt_var x \<Gamma> T \<rho>)
  from this wtenv_lookup obtain v where lx: "lookup x \<rho> = Some v" 
    and vt: "v \<in> WTV T" by blast
  from wt_var lx wt_env_lookup[of x \<Gamma> T \<rho>]  have wtv: "[] \<turnstile> v : T" by auto
  from lx wtv have "[\<rho>]FVar x = v" using msubst_var1 wt_dom_fv2 by simp
  with vt have "[\<rho>] FVar x \<in> WTV T" by simp
  with WTV_implies_WTE show "[\<rho>] FVar x \<in> WTE T" by auto
next
  case (wt_lambda L T1 \<Gamma> e T2 \<rho>)
  from wt_lambda have gr: "\<Gamma> \<turnstile> \<rho>" by simp
  from wt_lambda have wtr: "\<rho> \<in> WTENV \<Gamma>" by simp
  let ?L = "L @ (FV e) @ (FV ([\<rho>]e)) @ (map fst \<Gamma>) @ (map fst \<rho>)"
  have "[] \<turnstile> LambdaE ([\<rho>]e) : T1 \<rightarrow> T2" 
  proof
    show "\<forall>x. x \<notin> set ?L \<longrightarrow> [(x, T1)] \<turnstile> ({0\<rightarrow>FVar x} [\<rho>]e) : T2" 
    proof clarify
      fix x assume xl2: "x \<notin> set ?L"
      let ?G1 = "[(x,T1)]@\<Gamma>" and ?G2 = "\<Gamma>@[(x,T1)]"
      from xl2 wt_lambda have 3: "?G1 \<turnstile> ({0\<rightarrow>FVar x}e) : T2" by auto
      from xl2 have 4: "?G1 \<preceq> ?G2" using weaken_cons_snoc by auto
      from 3 4 have "?G2 \<turnstile> ({0\<rightarrow>FVar x}e) : T2" using env_weakening by blast
      with gr have 5: "[(x,T1)] \<turnstile> [\<rho>]({0\<rightarrow>FVar x}e) : T2" 
        using msubst_preserves_types by blast
      from xl2 have "assoc_dom \<rho> \<inter> set (FV (FVar x)) = {}" by simp
      with 5 gr msubst_permute 
      show "[(x,T1)] \<turnstile> ({0\<rightarrow>FVar x}([\<rho>]e)) : T2" by simp
    qed  
  qed
  hence wtlam: "[] \<turnstile>o LambdaE ([\<rho>]e) : T1 \<rightarrow> T2" by (rule adequacy1)
  have ibody: "\<forall>v\<in>WTV T1.\<exists>n v'. interp({0\<rightarrow>v}[\<rho>]e) n=Res v' \<and> v'\<in>WTV T2"
  proof
    fix v assume vt1: "v \<in> WTV T1"
    let ?X = "Suc (list_max [list_max L, list_max (FV e), list_max (FV ([\<rho>]e)), 
                           list_max (map fst \<Gamma>), list_max (map fst \<rho>)])"
    have xfv: "?X \<notin> set (FV e)" and xl: "?X \<notin> set L" 
      using list_max_fresh by auto
    from vt1 wtr have wtr2: "(?X,v)#\<rho> \<in> WTENV ((?X,T1)#\<Gamma>)" by simp
    from vt1 WTV_implies_WT adequacy2 have "[] \<turnstile> v : T1" by blast
    with gr have gr2: "((?X,T1)#\<Gamma>) \<turnstile> (?X,v)#\<rho>" by blast
    let ?E = "[((?X,v)#\<rho>)]({0\<rightarrow>FVar ?X}e)"
    from wt_lambda xl wtr2 gr2 have IH: "?E \<in> WTE T2" by blast
    from IH obtain v' n where ie: "interp ?E n = Res v'" and 
      wtvp: "v' \<in> WTV T2" by auto
    from vt1 have "FV v = []" 
      using WTV_implies_WT[of v T1] wt_dom_fv[of "[]" v T1] by simp
    hence drfv: "assoc_dom \<rho> \<inter> set (FV v) = {}" by simp
    have "?E = [\<rho>]([?X\<mapsto>v]({0\<rightarrow>FVar ?X}e))" by simp
    also with xfv have "... = [\<rho>]({0\<rightarrow>v}e)" 
      using decompose_subst[of "?X" e 0 v] by simp
    finally have "?E = {0\<rightarrow>v}[\<rho>]e"  
      using drfv gr msubst_permute[of \<rho> v \<Gamma> 0 e] by simp
    with ie wtvp
    show "\<exists> n v'. interp({0\<rightarrow>v}[\<rho>]e) n = Res v' \<and> v' \<in> WTV T2" by auto
  qed
  from wtlam ibody have lv: "LambdaE ([\<rho>]e) \<in> WTV (T1 \<rightarrow> T2)" by simp
  have il: "interp (LambdaE ([\<rho>]e)) (Suc 0) = Res (LambdaE ([\<rho>]e))" by simp
  from il lv have "LambdaE ([\<rho>]e) \<in> WTE (T1 \<rightarrow> T2)" by blast
  thus "[\<rho>](LambdaE e) \<in> WTE (T1 \<rightarrow> T2)" by simp
next
  case (wt_app \<Gamma> e1 T T' e2 \<rho>)
  from wt_app have "\<Gamma> \<turnstile> e1 : T \<rightarrow> T'" by simp
  from wt_app have IH1: "[\<rho>]e1 \<in> WTE (T \<rightarrow> T')" by simp
  from wt_app have IH2: "[\<rho>]e2 \<in> WTE T" by simp
  from IH1 obtain v1 n1 where ie1: "interp ([\<rho>]e1) n1 = Res v1" 
    and v1t: "v1 \<in> WTV (T\<rightarrow>T')" by force 
  from IH2 obtain v2 n2 where ie2: "interp ([\<rho>]e2) n2 = Res v2" 
    and v2t: "v2 \<in> WTV T" by (cases T) auto
  from v1t obtain e where v1: "v1 = LambdaE e" and
    app: "\<forall>v\<in>WTV T.\<exists>n v'. interp ({0\<rightarrow>v}e) n =Res v' \<and> v'\<in>WTV T'" by auto
  from v2t app obtain n3 v' where ie3: "interp ({0\<rightarrow>v2}e) n3 = Res v'"
    and vpt: "v' \<in> WTV T'" by auto
  let ?N = "n1 + n2 + n3"
  have n1n: "n1 \<le> ?N" and n2n: "n2 \<le> ?N" and n3n: "n3 \<le> ?N" by auto
  from ie1 n1n ie2 n2n ie3 n3n have ie1b: "interp ([\<rho>]e1) ?N = Res v1" and
    ie2b: "interp ([\<rho>]e2) ?N = Res v2" and 
    ie3b: "interp ({0\<rightarrow>v2}e) ?N = Res v'" using interp_mono by blast+
  from ie1b ie2b ie3b v1
  have "interp (AppE ([\<rho>]e1) ([\<rho>]e2)) (Suc ?N) = Res v'" by auto
  with vpt have "AppE ([\<rho>]e1) ([\<rho>]e2) \<in> WTE T'" by blast
  thus "[\<rho>]AppE e1 e2 \<in> WTE T'" by simp
qed

theorem WT_implies_iterp:
  fixes e::exp assumes wt: "[] \<turnstile> e : T"
  shows "\<exists> v n. interp e n = Res v \<and> [] \<turnstile> v : T"
proof -
  let ?R = "[]" and ?G = "[]"
  have 1: "?R \<in> WTENV []" by auto
  have 2: "[] \<turnstile> []" by auto
  from wt 1 2 have "[?R]e \<in> WTE T" by (rule WT_implies_WTE)
  hence 3: "e \<in> WTE T" by simp
  from 3 obtain v n where ev: "interp e n = Res v" and
    vt: "v \<in> WTV T" by auto
  from vt have "[] \<turnstile>o v : T" by (rule WTV_implies_WT)
  hence "[] \<turnstile> v : T" by (rule adequacy2)
  with ev show ?thesis by blast
qed
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
