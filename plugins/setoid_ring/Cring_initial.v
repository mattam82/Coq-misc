(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith_base.
Require Import Zpow_def.
Require Import BinInt.
Require Import BinNat.
Require Import Setoid.
Require Import Algebra_syntax.
Require Export Ring_polynom.
Require Export Cring.
Import List.

Set Implicit Arguments.

(* An object to return when an expression is not recognized as a constant *)
Definition NotConstant := false.

(** Z is a ring and a setoid*)

Lemma Zsth : Setoid_Theory Z (@eq Z).
constructor;red;intros;subst;trivial.
Qed.

Definition Zr : Cring Z.
apply (@Build_Cring Z Z0 (Zpos xH) Zplus Zmult Zminus Zopp (@eq Z)); 
try apply Zsth; try (red; red; intros; rewrite H; reflexivity). 
 exact Zplus_comm. exact Zplus_assoc.
 exact Zmult_1_l.  exact Zmult_assoc. exact Zmult_comm.
 exact Zmult_plus_distr_l. trivial. exact Zminus_diag.
Defined.

(** Two generic morphisms from Z to (abrbitrary) rings, *)
(**second one is more convenient for proofs but they are ext. equal*)
Section ZMORPHISM.
 Variable R : Type.
 Variable Rr: Cring R.
Existing Instance Rr.
 
 Ltac rrefl := gen_reflexivity Rr.

(*
Print HintDb typeclass_instances.
Print Scopes.
*)

 Fixpoint gen_phiPOS1 (p:positive) : R :=
  match p with
  | xH => 1
  | xO p => (1 + 1) * (gen_phiPOS1 p)
  | xI p => 1 + ((1 + 1) * (gen_phiPOS1 p))
  end.

 Fixpoint gen_phiPOS (p:positive) : R :=
  match p with
  | xH => 1
  | xO xH => (1 + 1)
  | xO p => (1 + 1) * (gen_phiPOS p)
  | xI xH => 1 + (1 +1)
  | xI p => 1 + ((1 + 1) * (gen_phiPOS p))
  end.

 Definition gen_phiZ1 z :=
  match z with
  | Zpos p => gen_phiPOS1 p
  | Z0 => 0
  | Zneg p => -(gen_phiPOS1 p)
  end.

 Definition gen_phiZ z :=
  match z with
  | Zpos p => gen_phiPOS p
  | Z0 => 0
  | Zneg p => -(gen_phiPOS p)
  end.
 Notation "[ x ]" := (gen_phiZ x).

 Definition get_signZ z :=
  match z with
  | Zneg p => Some (Zpos p)
  | _ => None
  end.

   Ltac norm := gen_cring_rewrite.
   Ltac add_push :=  gen_add_push.
Ltac rsimpl := simpl;  set_cring_notations.

 Lemma same_gen : forall x, gen_phiPOS1 x == gen_phiPOS x.
 Proof.
  induction x;rsimpl.
  cring_rewrite IHx. destruct x;simpl;norm.
  cring_rewrite IHx;destruct x;simpl;norm.
  gen_reflexivity.
 Qed.

 Lemma ARgen_phiPOS_Psucc : forall x,
   gen_phiPOS1 (Psucc x) == 1 + (gen_phiPOS1 x).
 Proof.
  induction x;rsimpl;norm.
  cring_rewrite IHx ;norm.
  add_push 1;gen_reflexivity.
 Qed.

 Lemma ARgen_phiPOS_add : forall x y,
   gen_phiPOS1 (x + y) == (gen_phiPOS1 x) + (gen_phiPOS1 y).
 Proof.
  induction x;destruct y;simpl;norm.
  cring_rewrite Pplus_carry_spec.
  cring_rewrite ARgen_phiPOS_Psucc.
  cring_rewrite IHx;norm.
  add_push (gen_phiPOS1 y);add_push 1;gen_reflexivity.
  cring_rewrite IHx;norm;add_push (gen_phiPOS1 y);gen_reflexivity.
  cring_rewrite ARgen_phiPOS_Psucc;norm;add_push 1;gen_reflexivity.
  cring_rewrite IHx;norm;add_push(gen_phiPOS1 y); add_push 1;gen_reflexivity.
  cring_rewrite IHx;norm;add_push(gen_phiPOS1 y);gen_reflexivity.
  add_push 1;gen_reflexivity.
  cring_rewrite ARgen_phiPOS_Psucc;norm;add_push 1;gen_reflexivity.
 Qed.

 Lemma ARgen_phiPOS_mult :
   forall x y, gen_phiPOS1 (x * y) == gen_phiPOS1 x * gen_phiPOS1 y.
 Proof.
  induction x;intros;simpl;norm.
  cring_rewrite ARgen_phiPOS_add;simpl;cring_rewrite IHx;norm.
  cring_rewrite IHx;gen_reflexivity.
 Qed.


(*morphisms are extensionaly equal*)
 Lemma same_genZ : forall x, [x] == gen_phiZ1 x.
 Proof.
  destruct x;rsimpl; try cring_rewrite same_gen; gen_reflexivity.
 Qed.

 Lemma gen_Zeqb_ok : forall x y,
   Zeq_bool x y = true -> [x] == [y].
 Proof.
  intros x y H.
  assert (H1 := Zeq_bool_eq x y H);unfold IDphi in H1.
  cring_rewrite H1;gen_reflexivity.
 Qed.

 Lemma gen_phiZ1_add_pos_neg : forall x y,
 gen_phiZ1
    match (x ?= y)%positive with
    | Eq => Z0
    | Lt => Zneg (y - x)
    | Gt => Zpos (x - y)
    end
 == gen_phiPOS1 x + -gen_phiPOS1 y.
 Proof.
  intros x y.
  assert (H0 := Pminus_mask_Gt x y). unfold Pgt in H0.
  assert (H1 := Pminus_mask_Gt y x). unfold Pgt in H1.
  rewrite Pos.compare_antisym in H1.
  destruct (Pos.compare_spec x y) as [H|H|H].
  subst. cring_rewrite cring_opp_def;gen_reflexivity.
  destruct H1 as [h [Heq1 [Heq2 Hor]]];trivial.
  unfold Pminus; cring_rewrite Heq1;rewrite <- Heq2.
  cring_rewrite ARgen_phiPOS_add;simpl;norm.
  cring_rewrite cring_opp_def;norm.
  destruct H0 as [h [Heq1 [Heq2 Hor]]];trivial.
  unfold Pminus; rewrite Heq1;rewrite <- Heq2.
  cring_rewrite ARgen_phiPOS_add;simpl;norm.
  set_cring_notations. add_push (gen_phiPOS1 h). cring_rewrite cring_opp_def ; norm.
 Qed.

 Lemma match_compOpp : forall x (B:Type) (be bl bg:B),
  match CompOpp x with Eq => be | Lt => bl | Gt => bg end
  = match x with Eq => be | Lt => bg | Gt => bl end.
 Proof. destruct x;simpl;intros;trivial. Qed.

 Lemma gen_phiZ_add : forall x y, [x + y] == [x] + [y].
 Proof.
  intros x y; repeat cring_rewrite same_genZ; generalize x y;clear x y.
  induction x;destruct y;simpl;norm.
  apply ARgen_phiPOS_add.
  apply gen_phiZ1_add_pos_neg.
  rewrite Pos.compare_antisym;simpl.
  cring_rewrite match_compOpp.
  cring_rewrite cring_add_comm.
  apply gen_phiZ1_add_pos_neg.
  cring_rewrite ARgen_phiPOS_add; norm.
 Qed.

Lemma gen_phiZ_opp : forall x, [- x] == - [x].
 Proof.
  intros x. repeat cring_rewrite same_genZ. generalize x ;clear x.
  induction x;simpl;norm.
  cring_rewrite cring_opp_opp.  gen_reflexivity.
 Qed.

 Lemma gen_phiZ_mul : forall x y, [x * y] == [x] * [y].
 Proof.
  intros x y;repeat cring_rewrite same_genZ.
  destruct x;destruct y;simpl;norm;
  cring_rewrite  ARgen_phiPOS_mult;try (norm;fail).
  cring_rewrite cring_opp_opp ;gen_reflexivity.
 Qed.

 Lemma gen_phiZ_ext : forall x y : Z, x = y -> [x] == [y].
 Proof. intros;subst;gen_reflexivity. Qed.

(*proof that [.] satisfies morphism specifications*)
 Lemma gen_phiZ_morph : @Cring_morphism Z R Zr Rr.
 apply (Build_Cring_morphism Zr Rr gen_phiZ);simpl;try gen_reflexivity.
   apply gen_phiZ_add. intros. cring_rewrite cring_sub_def. 
replace (x-y)%Z with (x + (-y))%Z. cring_rewrite gen_phiZ_add. 
cring_rewrite gen_phiZ_opp. gen_reflexivity.
reflexivity.
 apply gen_phiZ_mul. apply gen_phiZ_opp. apply gen_phiZ_ext. 
 Defined.

End ZMORPHISM.




