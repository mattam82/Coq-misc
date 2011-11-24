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
Require Import Coq.Relations.Relation_Definitions.

(** We will work with computational relations in general, and have specific instances
   for propositional relations for which we can prove more due to impredicativity of [Prop] *)

Notation crelation A := (A -> A -> Type).

(** We allow to unfold the [relation] definition while doing morphism search. *)

Notation inverse R := (flip R).

Definition complement {A} (R : crelation A) := fun x y => R x y -> False.

(** Opaque for proof-search. *)
Typeclasses Opaque complement.

(** These are convertible. *)

Lemma complement_inverse : forall A (R : crelation A), complement (inverse R) = inverse (complement R).
Proof. reflexivity. Qed.

(** We rebind relations in separate classes to be able to overload each proof. *)

Set Implicit Arguments.
Unset Strict Implicit.

Class Reflexive {A} (R : crelation A) :=
  reflexivity : forall x, R x x.

Class Irreflexive {A} (R : crelation A) :=
  irreflexivity : Reflexive (complement R).

Hint Extern 1 (Reflexive (complement _)) => class_apply @irreflexivity : typeclass_instances.

Class Symmetric {A} (R : crelation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Asymmetric {A} (R : crelation A) :=
  asymmetry : forall x y, R x y -> R y x -> False.

Class Transitive {A} (R : crelation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.

Hint Resolve @irreflexivity : ord.

Unset Implicit Arguments.

(** A HintDb for relations. *)

Ltac solve_relation :=
  match goal with
  | [ |- ?R ?x ?x ] => reflexivity
  | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
  end.

Hint Extern 4 => solve_relation : relations.

(** We can already dualize all these properties. *)

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

Lemma flip_Reflexive `{Reflexive A R} : Reflexive (flip R).
Proof. tauto. Qed.

Hint Extern 3 (Reflexive (flip _)) => apply flip_Reflexive : typeclass_instances.

Program Definition flip_Irreflexive `(Irreflexive A R) : Irreflexive (flip R) :=
  irreflexivity (R:=R).

Program Definition flip_Symmetric `(Symmetric A R) : Symmetric (flip R) :=
  fun x y H => symmetry (R:=R) H.

Program Definition flip_Asymmetric `(Asymmetric A R) : Asymmetric (flip R) :=
  fun x y H H' => asymmetry (R:=R) H H'.

Program Definition flip_Transitive `(Transitive A R) : Transitive (flip R) :=
  fun x y z H H' => transitivity (R:=R) H' H.

Hint Extern 3 (Irreflexive (flip _)) => class_apply flip_Irreflexive : typeclass_instances.
Hint Extern 3 (Symmetric (flip _)) => class_apply flip_Symmetric : typeclass_instances.
Hint Extern 3 (Asymmetric (flip _)) => class_apply flip_Asymmetric : typeclass_instances.
Hint Extern 3 (Transitive (flip _)) => class_apply flip_Transitive : typeclass_instances.

Definition Reflexive_complement_Irreflexive `(Reflexive A R)
   : Irreflexive (complement R).
Proof. firstorder. Qed.

Definition complement_Symmetric `(Symmetric A R) : Symmetric (complement R).
Proof. firstorder. Qed.

Hint Extern 3 (Symmetric (complement _)) => class_apply complement_Symmetric : typeclass_instances.
Hint Extern 3 (Irreflexive (complement _)) => class_apply Reflexive_complement_Irreflexive : typeclass_instances.

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

Ltac simpl_relation :=
  unfold flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ intuition ]).

Local Obligation Tactic := simpl_relation.

(** Logical implication. *)

Program Instance impl_Reflexive : Reflexive impl.
Program Instance impl_Transitive : Transitive impl.

(** Logical equivalence. *)

Instance iff_Reflexive : Reflexive iff := iff_refl.
Instance iff_Symmetric : Symmetric iff := iff_sym.
Instance iff_Transitive : Transitive iff := iff_trans.

(** Leibniz equality. *)

Instance eq_Reflexive {A} : Reflexive (@eq A) := @eq_refl A.
Instance eq_Symmetric {A} : Symmetric (@eq A) := @eq_sym A.
Instance eq_Transitive {A} : Transitive (@eq A) := @eq_trans A.

(** The Type arrow. *)

Program Instance arrow_Reflexive : Reflexive arrow.
Program Instance arrow_Transitive : Transitive arrow.

(** Identity. *)

Program Instance identity_Reflexive : Reflexive (@identity A).

Instance identity_Symmetric : Symmetric (@identity A).
  reduce. destruct H. reflexivity.
Defined.

Instance identity_Transitive : Transitive (@identity A).
  reduce. destruct H. assumption.
Defined.

(** Type isomorphism. *)

Class Iso (T T' : Type) := { 
  iso_l : T -> T'; 
  iso_r : T' -> T;
  iso_lr : forall x, iso_l (iso_r x) = x ;
  iso_rl : forall x, iso_r (iso_l x) = x
}.

Program Instance iso_Reflexive : Reflexive Iso := {
  reflexivity x := {| iso_l x := x ; iso_r x := x |} }.

Program Instance iso_Symmetric : Symmetric Iso := {
  symmetry x y isoxy := 
    {| iso_l := iso_r ; iso_r := iso_l; iso_lr := 
      iso_rl; iso_rl := iso_lr |} }.

Program Instance iso_Transitive : Transitive Iso := {
  transitivity A B C isoxy isoyz := 
    {| iso_l x := iso_l (iso_l x) ;
      iso_r x := iso_r (iso_r x) |} }.

  Next Obligation.
  Proof. now do 2 rewrite iso_lr. Defined.

  Next Obligation.
  Proof. now do 2 rewrite iso_rl. Defined.
    
(** Various combinations of reflexivity, symmetry and transitivity. *)

(** A [PreOrder] is both Reflexive and Transitive. *)

Class PreOrder {A} (R : crelation A) := {
  PreOrder_Reflexive :> Reflexive R | 2 ;
  PreOrder_Transitive :> Transitive R | 2 }.

(** A partial equivalence relation is Symmetric and Transitive. *)

Class PER {A} (R : crelation A) := {
  PER_Symmetric :> Symmetric R | 3 ;
  PER_Transitive :> Transitive R | 3 }.

(** Equivalence relations. *)

Class Equivalence {A} (R : crelation A) := {
  Equivalence_Reflexive :> Reflexive R ;
  Equivalence_Symmetric :> Symmetric R ;
  Equivalence_Transitive :> Transitive R }.

(** An Equivalence is a PER plus reflexivity. *)

Instance Equivalence_PER `(Equivalence A R) : PER R | 10 :=
  { PER_Symmetric := Equivalence_Symmetric ;
    PER_Transitive := Equivalence_Transitive }.

(** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)

Class Antisymmetric A eqA `{equ : Equivalence A eqA} (R : crelation A) :=
  antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

Program Definition flip_antiSymmetric `(Antisymmetric A eqA R) :
  Antisymmetric A eqA (flip R).
Proof. firstorder. Qed.

(** Leibinz equality [eq] is an equivalence relation.
   The instance has low priority as it is always applicable
   if only the type is constrained. *)

Program Instance eq_equivalence : Equivalence (@eq A) | 10.

(** Logical equivalence [iff] is an equivalence relation. *)

Program Instance iff_equivalence : Equivalence iff.

(** Type identity and isomorphism are equivalences *)

Program Instance identity_equivalence : Equivalence (@identity A) | 10.

Program Instance Iso_equivalence : Equivalence Iso | 9.

(** We now develop a generalization of results on relations for arbitrary predicates.
   The resulting theory can be applied to homogeneous binary relations but also to
   arbitrary n-ary predicates. *)

Local Open Scope list_scope.

(* Notation " [ ] " := nil : list_scope. *)
(* Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) (at level 1) : list_scope. *)

(** A compact representation of non-dependent arities, with the codomain singled-out. *)

(* Note, we do not use [list Type] because it imposes unnecessary universe constraints *)
Inductive Tlist : Type := Tnil : Tlist | Tcons : Type -> Tlist -> Tlist.
Local Infix "::" := Tcons.

Fixpoint arrows (l : Tlist) (r : Type) : Type :=
  match l with
    | Tnil => r
    | A :: l' => A -> arrows l' r
  end.

(** We can define abbreviations for operation and relation types based on [arrows]. *)

Definition unary_operation A := arrows (A::Tnil) A.
Definition binary_operation A := arrows (A::A::Tnil) A.
Definition ternary_operation A := arrows (A::A::A::Tnil) A.

(** We define n-ary [predicate]s as functions into [Prop]. *)

Notation predicate l := (arrows l Prop).

(** Unary predicates, or sets. *)

Definition unary_predicate A := predicate (A::Tnil).

(** Homogeneous binary relations, equivalent to [relation A]. *)

Definition binary_relation A := predicate (A::A::Tnil).

(** We can close a predicate by universal or existential quantification. *)

Fixpoint predicate_all (l : Tlist) : predicate l -> Prop :=
  match l with
    | Tnil => fun f => f
    | A :: tl => fun f => forall x : A, predicate_all tl (f x)
  end.

Fixpoint predicate_exists (l : Tlist) : predicate l -> Prop :=
  match l with
    | Tnil => fun f => f
    | A :: tl => fun f => exists x : A, predicate_exists tl (f x)
  end.

(** Pointwise extension of a binary operation on [T] to a binary operation
   on functions whose codomain is [T].
   For an operator on [Prop] this lifts the operator to a binary operation. *)

Fixpoint pointwise_extension {T : Type} (op : binary_operation T)
  (l : Tlist) : binary_operation (arrows l T) :=
  match l with
    | Tnil => fun R R' => op R R'
    | A :: tl => fun R R' =>
      fun x => pointwise_extension op tl (R x) (R' x)
  end.

(** Pointwise lifting, equivalent to doing [pointwise_extension] and closing using [predicate_all]. *)

Fixpoint pointwise_lifting (op : binary_relation Prop)  (l : Tlist) : binary_relation (predicate l) :=
  match l with
    | Tnil => fun R R' => op R R'
    | A :: tl => fun R R' =>
      forall x, pointwise_lifting op tl (R x) (R' x)
  end.

(** The n-ary equivalence relation, defined by lifting the 0-ary [iff] relation. *)

Definition predicate_equivalence {l : Tlist} : binary_relation (predicate l) :=
  pointwise_lifting iff l.

(** The n-ary implication relation, defined by lifting the 0-ary [impl] relation. *)

Definition predicate_implication {l : Tlist} :=
  pointwise_lifting impl l.

(** Notations for pointwise equivalence and implication of predicates. *)

Infix "<∙>" := predicate_equivalence (at level 95, no associativity) : predicate_scope.
Infix "-∙>" := predicate_implication (at level 70, right associativity) : predicate_scope.

Open Local Scope predicate_scope.

(** The pointwise liftings of conjunction and disjunctions.
   Note that these are [binary_operation]s, building new relations out of old ones. *)

Definition predicate_intersection := pointwise_extension and.
Definition predicate_union := pointwise_extension or.

Infix "/∙\" := predicate_intersection (at level 80, right associativity) : predicate_scope.
Infix "\∙/" := predicate_union (at level 85, right associativity) : predicate_scope.

(** The always [True] and always [False] predicates. *)

Fixpoint true_predicate {l : Tlist} : predicate l :=
  match l with
    | Tnil => True
    | A :: tl => fun _ => @true_predicate tl
  end.

Fixpoint false_predicate {l : Tlist} : predicate l :=
  match l with
    | Tnil => False
    | A :: tl => fun _ => @false_predicate tl
  end.

Notation "∙⊤∙" := true_predicate : predicate_scope.
Notation "∙⊥∙" := false_predicate : predicate_scope.

(** Predicate equivalence is an equivalence, and predicate implication defines a preorder. *)

Program Instance predicate_equivalence_equivalence : Equivalence (@predicate_equivalence l).

  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    fold pointwise_lifting.
    induction l. firstorder.
    intros. simpl in *. pose (IHl (x x0) (y x0) (z x0)).
    firstorder.
  Qed.

Program Instance predicate_implication_preorder :
  PreOrder (@predicate_implication l).
  Next Obligation.
    induction l ; firstorder.
  Qed.
  Next Obligation.
    induction l. firstorder.
    unfold predicate_implication in *. simpl in *.
    intro. pose (IHl (x x0) (y x0) (z x0)). firstorder.
  Qed.

(** We define the various operations which define the algebra on binary 
   propositional relations, from the general ones. *)

Definition relation_equivalence {A : Type} : relation (relation A) :=
  @predicate_equivalence (_::_::Tnil).

Definition relation_implication {A:Type} : relation (relation A) :=
  @predicate_implication (A::A::Tnil).

Definition relation_conjunction {A} (R : relation A) (R' : relation A) : relation A :=
  @predicate_intersection (A::A::Tnil) R R'.

Definition relation_disjunction {A} (R : relation A) (R' : relation A) : relation A :=
  @predicate_union (A::A::Tnil) R R'.

(** Relation equivalence is an equivalence, and subrelation defines a partial order. *)

Set Automatic Introduction.

Instance relation_equivalence_equivalence (A : Type) :
  Equivalence (@relation_equivalence A).
Proof. exact (@predicate_equivalence_equivalence (A::A::Tnil)). Qed.

Instance relation_implication_preorder A : PreOrder (@relation_implication A).
Proof. exact (@predicate_implication_preorder (A::A::Tnil)). Qed.

Definition crelation_conjunction {A} (R R' : crelation A) : crelation A :=
  fun x y => (R x y * R' x y)%type.

Definition crelation_disjunction {A} (R R' : crelation A) : crelation A :=
  fun x y => (R x y + R' x y)%type.

(** We define the various operations which define the algebra on binary 
   computational relations directly to avoid inconsistencies. *)

(* Definition crelation_equivalence {A : Type} : crelation (crelation A) := *)
(*   fun R R' => forall x y, Iso (R x y) (R' x y). *)

Definition crelation_equivalence {A : Type} : crelation (crelation A) :=
  fun R R' => forall x y, ((R x y -> R' x y) * (R' x y -> R x y)).

Class subrelation {A} (R R' : crelation A) :=
  is_subrelation : forall x y, R x y -> R' x y.

Arguments subrelation {A} R R'.

Instance crelation_equivalence_equivalence (A : Type) :
  Equivalence (@crelation_equivalence A).
Proof. unfold crelation_equivalence. split; red; intros; firstorder.
  now apply X0, X.
  now apply X, X0.
Defined.

Instance crelation_implication_preorder A : PreOrder (@subrelation A).
Proof. split; red; intros; firstorder. Defined.


(** *** Partial Order.
   A partial order is a preorder which is additionally antisymmetric.
   We give an equivalent definition, up-to an equivalence relation
   on the carrier. *)

Class PartialOrder {A} (eqA : relation A) `{equ : Equivalence A eqA} (R : relation A) `{preo : PreOrder A R} :=
  partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (inverse R)).

Class CPartialOrder {A} eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} :=
  cpartial_order_equivalence : crelation_equivalence eqA (crelation_conjunction R (inverse R)).

(** The equivalence proof is sufficient for proving that [R] must be a morphism
   for equivalence (see Morphisms).
   It is also sufficient to show that [R] is antisymmetric w.r.t. [eqA] *)

Instance partial_order_antisym `(PartialOrder A eqA R) : ! Antisymmetric A eqA R.
Proof with auto.
  reduce_goal.
  pose proof partial_order_equivalence as poe. repeat red in poe.
  specialize (poe x y). apply poe; firstorder.
Defined.

Instance cpartial_order_antisym `(CPartialOrder A eqA R) : ! Antisymmetric A eqA R.
Proof with auto.
  reduce_goal.
  pose proof cpartial_order_equivalence as poe. repeat red in poe.
  specialize (poe x y). apply poe; firstorder.
Defined.

(** The partial order defined by subrelation and relation equivalence. *)

Program Instance subrelation_partial_order :
  ! PartialOrder (relation A) relation_equivalence relation_implication.

  Next Obligation.
  Proof. unfold relation_equivalence in *; compute; firstorder. Defined.


(* Program Definition creleq_conj_subrel A (R R' : crelation A)  *)
(*   (H : crelation_conjunction subrelation (inverse subrelation) R R') : *)
(*   crelation_equivalence R R' := *)
(*   fun x y => {| iso_l := fst H x y ; iso_r := snd H x y |}.  *)

(*   Next Obligation. *)
(*   Proof. red in H. *)
(*     destruct H. red in s, s0. simpl.  *)
(*  destruct H. simpl.  *)

(* Program Instance crelation_partial_order : *)
(*   ! CPartialOrder (relation A) crelation_equivalence subrelation. *)

(*   Next Obligation. *)
(*   Proof. *)
(*     unfold crelation_equivalence, crelation_conjunction. *)
(*     unfold subrelation. firstorder. *)
(*   Defined. *)

Typeclasses Opaque arrows predicate_implication predicate_equivalence
  relation_equivalence pointwise_lifting.

(** Rewrite relation on a given support: declares a relation as a rewrite
   relation for use by the generalized rewriting tactic.
   It helps choosing if a rewrite should be handled
   by the generalized or the regular rewriting tactic using leibniz equality.
   Users can declare an [RewriteRelation A RA] anywhere to declare default
   relations. This is also done automatically by the [Declare Relation A RA]
   commands. *)

Class RewriteRelation {A : Type} (RA : crelation A).

Instance: RewriteRelation impl.
Instance: RewriteRelation iff.
Instance: RewriteRelation (@relation_equivalence A).
Instance: RewriteRelation (@crelation_equivalence A).
Instance: RewriteRelation (@subrelation A).
Instance: RewriteRelation (@identity A).
Instance: RewriteRelation Iso.

(** Any [Equivalence] declared in the context is automatically considered
   a rewrite relation. *)

Instance equivalence_rewrite_relation `(Equivalence A eqA) : RewriteRelation eqA.

(** Strict Order *)

Class StrictOrder {A : Type} (R : crelation A) := {
  StrictOrder_Irreflexive :> Irreflexive R ;
  StrictOrder_Transitive :> Transitive R
}.

Instance StrictOrder_Asymmetric `(StrictOrder A R) : Asymmetric R.
Proof. firstorder. Qed.

(** Inversing a [StrictOrder] gives another [StrictOrder] *)

Lemma StrictOrder_inverse `(StrictOrder A R) : StrictOrder (inverse R).
Proof. firstorder. Qed.

(** Same for [PartialOrder], for [relation]s only.  *)

Lemma PreOrder_inverse `(PreOrder A (R : relation A)) : PreOrder (inverse R).
Proof. firstorder. Qed.

Hint Extern 3 (StrictOrder (inverse _)) => class_apply StrictOrder_inverse : typeclass_instances.
Hint Extern 3 (PreOrder (inverse _)) => class_apply PreOrder_inverse : typeclass_instances.

Lemma PartialOrder_inverse `(PartialOrder A eqA (R : relation A)) : PartialOrder eqA (inverse R).
Proof. firstorder. Qed.

Hint Extern 3 (PartialOrder (inverse _)) => class_apply PartialOrder_inverse : typeclass_instances.
