(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Typeclass-based relations, tactics and standard instances

   This is the basic theory needed to formalize morphisms and setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Relation_Definitions.

Notation crelation A := (A -> A -> Type).

(** We allow to unfold the [relation] definition while doing morphism search. *)

Inductive inverse {A} (R : crelation A) : crelation A :=
| crel_inv x y : R x y -> inverse R y x.

Lemma inverse_inv {A} (R : crelation A) x y : inverse R x y -> R y x.
Proof. intros. now destruct X. Defined.

Definition complement {A} (R : crelation A) : crelation A := fun x y => R x y -> False.

(** Opaque for proof-search. *)
Typeclasses Opaque complement.

(** These are convertible. *)

Lemma complement_inverse : forall A (R : crelation A), complement (inverse R) = inverse (complement R).
Proof. intros.  unfold complement. Admitted.

(** We rebind crelations in separate classes to be able to overload each proof. *)

Set Implicit Arguments.
Unset Strict Implicit.

Class CReflexive {A} (R : crelation A) :=
  creflexivity : forall x, R x x.

Class CIrreflexive {A} (R : crelation A) :=
  cirreflexivity : CReflexive (complement R).

Hint Extern 1 (CReflexive (complement _)) => class_apply @cirreflexivity : typeclass_instances.

Class CSymmetric {A} (R : crelation A) :=
  csymmetry : forall x y, R x y -> R y x.

Class CAsymmetric {A} (R : crelation A) :=
  casymmetry : forall x y, R x y -> R y x -> False.

Class CTransitive {A} (R : crelation A) :=
  ctransitivity : forall x y z, R x y -> R y z -> R x z.

Hint Resolve @cirreflexivity : ord.

Unset Implicit Arguments.

(** A HintDb for crelations. *)

Ltac solve_crelation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

Hint Extern 4 => solve_crelation : crelations.

(** We can already dualize all these properties. *)

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

Lemma flip_CReflexive `{CReflexive A R} : CReflexive (flip R).
Proof. tauto. Qed.

Hint Extern 3 (CReflexive (flip _)) => apply flip_CReflexive : typeclass_instances.

Program Definition flip_CIrreflexive `(CIrreflexive A R) : CIrreflexive (flip R) :=
  cirreflexivity (R:=R).

Program Definition flip_CSymmetric `(CSymmetric A R) : CSymmetric (flip R) :=
  fun x y H => csymmetry (R:=R) H.

Program Definition flip_CAsymmetric `(CAsymmetric A R) : CAsymmetric (flip R) :=
  fun x y H H' => casymmetry (R:=R) H H'.

Program Definition flip_CTransitive `(CTransitive A R) : CTransitive (flip R) :=
  fun x y z H H' => ctransitivity (R:=R) H' H.

Hint Extern 3 (CIrreflexive (flip _)) => class_apply flip_CIrreflexive : typeclass_instances.
Hint Extern 3 (CSymmetric (flip _)) => class_apply flip_CSymmetric : typeclass_instances.
Hint Extern 3 (CAsymmetric (flip _)) => class_apply flip_CAsymmetric : typeclass_instances.
Hint Extern 3 (CTransitive (flip _)) => class_apply flip_CTransitive : typeclass_instances.

Definition CReflexive_complement_CIrreflexive `(CReflexive A (R : crelation A))
   : CIrreflexive (complement R).
Proof. firstorder. Qed.

Definition complement_CSymmetric `(CSymmetric A (R : crelation A)) : CSymmetric (complement R).
Proof. firstorder. Qed.

Hint Extern 3 (CSymmetric (complement _)) => class_apply complement_CSymmetric : typeclass_instances.
Hint Extern 3 (CIrreflexive (complement _)) => class_apply CReflexive_complement_CIrreflexive : typeclass_instances.

(** * Standard instances. *)

Ltac reduce_hyp H :=
  match type of H with
    | context [ _ <-> _ ] => fail 1
    | _ => red in H ; try reduce_hyp H
  end.

Ltac reduce_goal :=
  match goal with
    | [ |- _ <-> _ ] => fail 1
    | _ => red ; intros ; try reduce_goal
  end.

Tactic Notation "reduce" "in" hyp(Hid) := reduce_hyp Hid.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) :=
  first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
    refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

Ltac simpl_crelation :=
  unfold flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ intuition ]).

Local Obligation Tactic := simpl_crelation.

(** Logical implication. *)

Program Instance impl_CReflexive : CReflexive impl.
Program Instance impl_Transitive : CTransitive impl.

(** Logical equivalence. *)

Instance iff_CReflexive : CReflexive iff := iff_refl.
Instance iff_CSymmetric : CSymmetric iff := iff_sym.
Instance iff_CTransitive : CTransitive iff := iff_trans.

(** Leibniz equality. *)

Instance eq_CReflexive {A} : CReflexive (@eq A) := @eq_refl A.
Instance eq_CSymmetric {A} : CSymmetric (@eq A) := @eq_sym A.
Instance eq_CTransitive {A} : CTransitive (@eq A) := @eq_trans A.

(** Various combinations of reflexivity, symmetry and transitivity. *)

(** A [CPreOrder] is both CReflexive and CTransitive. *)

Class CPreOrder {A} (R : crelation A) := {
  CPreOrder_CReflexive :> CReflexive R | 2 ;
  CPreOrder_CTransitive :> CTransitive R | 2 }.

(** A partial equivalence crelation is CSymmetric and CTransitive. *)

Class CPER {A} (R : crelation A) := {
  CPER_CSymmetric :> CSymmetric R | 3 ;
  CPER_CTransitive :> CTransitive R | 3 }.

(** Equivalence crelations. *)

Class CEquivalence {A} (R : crelation A) := {
  CEquivalence_CReflexive :> CReflexive R ;
  CEquivalence_CSymmetric :> CSymmetric R ;
  CEquivalence_CTransitive :> CTransitive R }.

(** An CEquivalence is a CPER plus reflexivity. *)

Instance CEquivalence_CPER `(CEquivalence A R) : CPER R | 10 :=
  { CPER_CSymmetric := CEquivalence_CSymmetric ;
    CPER_CTransitive := CEquivalence_CTransitive }.

(** We can now define antisymmetry w.r.t. an equivalence crelation on the carrier. *)

Class CAntisymmetric A eqA `{equ : CEquivalence A eqA} (R : crelation A) :=
  cantisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

Program Definition flip_antiCSymmetric `(CAntisymmetric A eqA R) :
  CAntisymmetric A eqA (flip R).
Proof. firstorder. Qed.

(** Leibinz equality [eq] is an equivalence crelation.
   The instance has low priority as it is always applicable
   if only the type is constrained. *)

Program Instance eq_equivalence : CEquivalence (@eq A) | 10.

(** Logical equivalence [iff] is an equivalence crelation. *)

Program Instance iff_equivalence : CEquivalence iff.

(** The Type arrow. *)

Program Instance arrow_CReflexive : CReflexive arrow.
Program Instance arrow_CTransitive : CTransitive arrow.

(** Identity. *)

Program Instance identity_CReflexive : CReflexive (@identity A).

Instance identity_CSymmetric : CSymmetric (@identity A).
  reduce. destruct H. reflexivity.
Defined.

Instance identity_CTransitive : CTransitive (@identity A).
  reduce. destruct H. assumption.
Defined.

(** Type inhabitance. *)

Record iso (T T' : Type) := { iso_l : T -> T'; iso_r : T' -> T }.

Program Instance iso_CReflexive : CReflexive iso.
Program Instance iso_CSymmetric : CSymmetric iso.
Program Instance iso_CTransitive : CTransitive iso.

(** We define the various operations which define the algebra on binary crelations.
   They are defined as inductives to profit from universe polymorphism.
 *)

Inductive crelation_equivalence {A : Type} (R R' : crelation A) :=
| crelation_equiv : (forall x y, iso (R x y) (R' x y)) -> crelation_equivalence R R'.

Inductive crelation_implication {A : Type} (R R' : crelation A) :=
| crelation_impl : (forall x y, R x y -> R' x y) -> crelation_implication R R'.

Class subcrelation {A:Type} (R R' : crelation A) :=
  { is_subrelation : crelation_implication R R' }.

Implicit Arguments subcrelation [[A]].

Inductive crelation_conjunction {A} (R : crelation A) (R' : crelation A) : crelation A :=
  crelation_conj x y : R x y -> R' x y -> crelation_conjunction R R' x y.

Inductive crelation_disjunction {A} (R : crelation A) (R' : crelation A) : crelation A :=
| crelation_disj_l x y : R x y -> crelation_disjunction R R' x y
| crelation_disj_r x y : R' x y -> crelation_disjunction R R' x y.

(** Relation equivalence is an equivalence, and subcrelation defines a partial order. *)

Set Automatic Introduction.

Instance crelation_equivalence_equivalence (A : Type) :
  CEquivalence (@crelation_equivalence A).
Proof. split; red; intro. firstorder. firstorder. 
  intuition. constructor. destruct X; destruct X0. intros. destruct (i x0 y0). 
  destruct (i0 x0 y0). firstorder. 
Defined.

Instance crelation_implication_preorder A : CPreOrder (@subcrelation A) := {}.
Proof. red. intros; firstorder. 
  repeat red. intros. firstorder. 
Defined.

(** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence crelation
   on the carrier. *)

Class CPartialOrder {A} eqA `{equ : CEquivalence A eqA} R `{preo : CPreOrder A R} :=
  cpartial_order_equivalence : crelation_equivalence eqA (crelation_conjunction R (inverse R)).

(** The equivalence proof is sufficient for proving that [R] must be a morphism
   for equivalence (see Morphisms).
   It is also sufficient to show that [R] is antisymmetric w.r.t. [eqA] *)

Instance partial_order_antisym `(CPartialOrder A eqA R) : ! CAntisymmetric A eqA R.
Proof with auto.
  reduce_goal.
  pose proof cpartial_order_equivalence as poe. repeat red in poe.
  apply poe. constructor; firstorder.
  constructor. auto.
Defined.


(** The partial order defined by subrelation and relation equivalence. *)

(** Rewrite crelation on a given support: declares a crelation as a rewrite
   crelation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   crelations. This is also done automatically by the [Declare Relation A RA]
   commands. *)

Class CRewriteRelation {A : Type} (RA : crelation A).

Instance: CRewriteRelation impl.
Instance: CRewriteRelation iff.
Instance: CRewriteRelation (@crelation_equivalence A).
Instance: CRewriteRelation iso.

(** Any [CEquivalence] declared in the context is automatically considered
   a rewrite crelation. *)

Instance equivalence_rewrite_crelation `(CEquivalence A eqA) : CRewriteRelation eqA.

(** Strict Order *)

Class CStrictOrder {A : Type} (R : crelation A) := {
  StrictOrder_CIrreflexive :> CIrreflexive R ;
  StrictOrder_CTransitive :> CTransitive R
}.

Instance CStrictOrder_Asymmetric `(CStrictOrder A R) : CAsymmetric R.
Proof. firstorder. Qed.

(** Inversing a [StrictOrder] gives another [StrictOrder] *)

Lemma CStrictOrder_inverse `(CStrictOrder A R) : CStrictOrder (inverse R).
Proof. constructor. red. red. intros. red. intros. apply inverse_inv in X. 
  apply (cirreflexivity X).  

  constructor. apply inverse_inv in X; apply inverse_inv in X0.
  pose (ctransitivity (R:=R)). firstorder.
Defined.

(** Same for [PartialOrder]. *)

Instance CPreOrder_inverse `(CPreOrder A R) : CPreOrder (inverse R).
Proof. constructor. constructor. apply (creflexivity (R:=R)).
   constructor. apply inverse_inv in X; apply inverse_inv in X0. 
   generalize (ctransitivity (R:=R)). firstorder.
Defined.

Lemma CPartialOrder_inverse `(CPartialOrder A eqA R) : CPartialOrder eqA (inverse R).
Proof. firstorder. specialize (i x y). destruct i.
  specialize (iso_l0 X). 
  constructor. constructor. destruct iso_l0. now apply inverse_inv in i.

  repeat constructor. now destruct iso_l0. 

  destruct (i x y).
  apply iso_r0. destruct X. do 2 apply inverse_inv in i1.
  now constructor.
Defined.

Hint Extern 3 (CPartialOrder (inverse _)) => class_apply CPartialOrder_inverse : typeclass_instances.
