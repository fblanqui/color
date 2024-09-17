(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-09-17


* Structures for types equipped with a comparison function.
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil RelUtil SN EqUtil.
From Coq.Structures Require Export OrderedType.

(***********************************************************************)
(** Properties of [CompOpp]. *)

Lemma CompOpp_eq : forall c d, CompOpp c = CompOpp d <-> c = d.

Proof. destruct c; destruct d; simpl; intuition; discr. Qed.

(***********************************************************************)
(** Structure for a type equipped with a comparison function. *)

Module Type Cmp.

  Parameter t : Type.

  Parameter cmp : t -> t -> comparison.

  Parameter cmp_opp : forall x y, cmp x y = CompOpp (cmp y x).

End Cmp.

(** Properties of types equipped with a comparison function. *)

Module CmpFacts (Import C : Cmp).

  Definition eq : relation t := fun x y => cmp x y = Eq.

  Definition lt : relation t := fun x y => cmp x y = Lt.

  Global Instance eq_refl : Reflexive eq.

  Proof.
    intro x. unfold eq. case_eq (cmp x x); intro h.
    refl.
    gen h. rewrite cmp_opp, h. discr.
    gen h. rewrite cmp_opp, h. discr.
  Qed.

  Global Instance eq_sym : Symmetric eq.

  Proof. intros x y. unfold eq. intro xy. rewrite cmp_opp, xy. refl. Qed.

  Lemma lt_not_eq x y : lt x y -> ~eq x y.

  Proof. unfold lt, eq. intro xy. rewrite xy. discr. Qed.

  Lemma compare x y : Compare lt eq x y.

  Proof.
    case_eq (cmp x y); intro h.
    apply EQ. hyp.
    apply LT. hyp.
    apply GT. unfold lt. rewrite cmp_opp, h. refl.
  Qed.

End CmpFacts.

(***********************************************************************)
(** Structure for a type equipped with a comparison function that is
transitive. The type is therefore totally ordered. This structure is
equivalent to [Structures.OrderedTypeAlt]. *)

Module Type CmpTrans.

  Include Cmp.

  Parameter cmp_eq_trans :
    forall x y z, cmp x y = Eq -> cmp y z = Eq -> cmp x z = Eq.

  Parameter cmp_lt_trans :
    forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.

End CmpTrans.

(** Properties of types equipped with a comparison function that is
transitive. *)

Module CmpTransFacts (Import CT : CmpTrans).

  Include CmpFacts CT.

  Global Instance eq_trans : Transitive eq.

  Proof. intros x y z. apply cmp_eq_trans. Qed.

  Global Instance lt_trans : Transitive lt.

  Proof. intros x y z. apply cmp_lt_trans. Qed.

End CmpTransFacts.

(***********************************************************************)
(** Functor buiding a MiniOrderedType structure from a CmpTrans
structure. *)

Module MOT_of_CmpTrans (Import CT : CmpTrans) <: MiniOrderedType.

  Definition t := t.

  Include CmpTransFacts CT.

End MOT_of_CmpTrans.

(***********************************************************************)
(** Structure for a type equipped with a transitive comparison
function whose equivalence is Leibniz equality. *)

Module Type CmpTransLeibniz.

  Include Cmp.

  Parameter cmp_eq : forall x y, cmp x y = Eq -> x = y.

  Parameter cmp_lt_trans :
    forall x y z, cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.

End CmpTransLeibniz.

(** Functor building a CmpTrans structure from a CmpTransLeibniz structure. *)

Module CmpTrans_of_CmpTransLeibniz (CTL : CmpTransLeibniz) <: CmpTrans.

  Include CTL.

  Module Import CF := CmpFacts CTL.
  
  Lemma cmp_eq_trans x y z : cmp x y = Eq -> cmp y z = Eq -> cmp x z = Eq.

  Proof.
    intros xy yz. apply cmp_eq in xy. apply cmp_eq in yz. subst. apply eq_refl.
  Qed.

End CmpTrans_of_CmpTransLeibniz.

(** Functor building a MiniOrderedType structure from a
CmpTransLeibniz structure. *)

Module MOT_of_CmpTransLeibniz (Import CTL : CmpTransLeibniz) <: MiniOrderedType.

  Definition t := t.

  Include LeibnizFacts CTL.

  Definition lt : relation t := fun x y => cmp x y = Lt.

  Global Instance lt_trans : Transitive lt.

  Proof. intros x y z. apply cmp_lt_trans. Qed.

  Lemma lt_not_eq x y : lt x y -> x <> y.

  Proof.
    unfold lt. intros xy e. subst y. gen xy. rewrite cmp_opp, xy. discr.
  Qed.

  Lemma compare x y : Compare lt eq x y.

  Proof.
    case_eq (cmp x y); intro h.
    apply EQ. apply cmp_eq. hyp.
    apply LT. hyp.
    apply GT. unfold lt. rewrite cmp_opp, h. refl.
  Qed.

End MOT_of_CmpTransLeibniz.
