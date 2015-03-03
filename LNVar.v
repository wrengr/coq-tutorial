(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * Free variables/names for the locally nameless style.

cf <http://www.chargueraud.org/viewcoq.php?sFile=softs%2Ftlc%2Fsrc%2FLibVar.v>
*)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* [Coq.Classes.EquivDec] is Coq 8.3 only *)
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import WrengrUtil.Tactics.Introv.
Require Import WrengrUtil.CoqExtras.Nat.
Require Export LNSet.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * The specification of a variable type. *)
Class VarType (Var : Set) `{eqdec0 : EqDec Var eq} :=
    { inhabVar : inhabited Var
    ; freshVar : forall (xs:set Var), { x:Var | x \notin xs }
    }.


(*
(** * The specification of a variable type. *)
Module Type VarType.

    (** We leave the type of variables abstract. *)    
    Parameter Var : Set.
    
    (** This type is inhabited. *) (* TODO: who cares? *)
    Parameter inhabVar : inhabited Var.
    
    (** We can decide equality on this type. *)
    Parameter _VarEqDec : EqDec Var eq. (* Defines [equiv_dec] *)
    Program Instance VarEqDec : EqDec Var eq := _VarEqDec.
    
    (** Finally, we have a means of generating fresh variables. *)
    Parameter freshVar : forall (xs:set Var), { x:Var | x \notin xs }.

End VarType.
*)


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** * A concrete implementation using [nat]. *)

(* Module Export NatVar : VarType. *)
Section NatVar.

    Definition NatVar := nat.

    Lemma inhabNatVar : inhabited NatVar.
    Proof. apply inhabits. apply 0. Qed.
    
    Program Instance NatVarEqDec : EqDec NatVar eq := nat_eq_eqdec.
    
    (** The method for generating a new variable. *)
    Definition genNatVar (xs:set NatVar) : NatVar :=
        1 + fold_right plus 0 xs.
    
    (** A lemma for proving [freshNatVar_spec]. *)
    Lemma genNatVar_gt : forall xs x, x \in xs -> x < genNatVar xs.
    Proof.
      unfold genNatVar. induction xs as [ | x0 xs0 IHxs0 ]; introv I.
        contradiction.
        
        destruct I as [H | I']; simpl.
          rewrite H.
          auto with arith.
          (* Or:
          rewrite plus_Snm_Sn_m.
          apply lt_plus_trans.
          apply lt_n_Sn.
          *)
          
          simpl in IHxs0.
          (* [auto with arith] can's solve any part of this. Is the [plus_Snm_n_Sm] hint really in there?? *)
          rewrite plus_Snm_n_Sm.
          rewrite plus_comm.
          apply lt_plus_trans.
          apply IHxs0.
          exact I'.
    Qed.
    
    (** Proof that [genNatVar] satisfies the specification of [freshNatVar]. *)
    Lemma freshNatVar_spec : forall xs, (genNatVar xs) \notin xs.
    Proof.
      unfold genNatVar, not. intros xs H.
      destruct xs as [|x0 xs0]; simpl.
        assumption.
        
        inversion_clear H as [H0|H0]; simpl in H0.
          rewrite plus_comm in H0.
          exact (succ_plus_discr _ _ H0).
          
          apply genNatVar_gt    in H0.
          unfold genNatVar      in H0.
          rewrite plus_Snm_n_Sm in H0.
          destruct x0.
            exact (lt_irrefl _ H0).
            
            assert (H1 : forall x y, ~ S x + y < y) by auto with arith.
            exact (H1 _ _ H0).
    Qed.
    
    Lemma freshNatVar : forall (xs:set NatVar), { x:NatVar | x \notin xs }.
    Proof. intros xs. exists (genNatVar xs). apply freshNatVar_spec. Qed.

    Instance NatVarType : VarType NatVar :=
        { inhabVar := inhabNatVar
        ; freshVar := freshNatVar
        }.
End NatVar.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* N.B., must use a section in order to use [Context], and must use
    [Context] instead of [Variable] if we want it to be implicit.
    However, we can't define notations inside sections if we want
    them to last. *)
Section DerivedOperations.
Context  {Var : Set}.
Context `{VT : VarType Var}.


(** Freshness of [n] variables [ys] from a set [xs] and from one another. *)
Fixpoint Fresh (xs:set Var) (n:nat) (ys:set Var) {struct ys} : Prop :=
    match ys, n with
    | nil,    O    => True
    | y::ys', S n' => y \notin xs /\ Fresh (y \a xs) n' ys'
    | _,      _    => False
    end.
(* TODO: How is this different than [Hint Unfold Fresh]? *)
Hint Extern 1 (Fresh _ _ _) => simpl.


(** Generate [n] variables fresh from [xs] and one another. *)
Lemma freshVars : forall xs n, { ys:set Var | Fresh xs n ys }.
Proof.
  intros. generalize dependent xs. induction n; intros xs;
    [ exists nil; auto
    | destruct (freshVar xs)   as [y  Hy]
    ; destruct (IHn (y \a xs)) as [ys Hys]
    ; exists (y::ys); auto
    ].
Qed.
End DerivedOperations.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin. *)
