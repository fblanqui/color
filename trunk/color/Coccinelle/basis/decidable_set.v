(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

(* dummy Require Import Relations. *)
Require Import Relation_Definitions.
Require Import Setoid.
Require Import Bool.
Require Import Arith.

Module Type S.

Parameter A : Type.
Parameter eq_bool : A -> A -> bool.
Parameter eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => a1 = a2 | false => ~ a1 = a2 end.

End S.

Module Type ES.

Parameter A : Type.
Parameter eq_A : relation A.
Parameter eq_bool : A -> A -> bool.
Parameter eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => eq_A a1 a2 | false => ~eq_A a1 a2 end.

Parameter eq_proof : equivalence A eq_A.

  Add Relation A eq_A 
  reflexivity proved by (@equiv_refl _ _ eq_proof)
    symmetry proved by (@equiv_sym _ _ eq_proof)
      transitivity proved by (@equiv_trans _ _ eq_proof) as EQA.

End ES.

Module Convert (DS : S) <: 
  ES with Definition A := DS.A
       with Definition eq_A := @eq DS.A.

Definition A := DS.A.
Definition eq_A := @eq A.
Definition eq_bool := DS.eq_bool.
Definition eq_bool_ok := DS.eq_bool_ok.

Lemma eq_proof : equivalence A eq_A.
Proof.
unfold eq_A; split.
intro a; reflexivity.
intros a1 a2 a3 H1 H2; transitivity a2; trivial.
intros a1 a2 H; symmetry; trivial.
Qed.

Add Relation A eq_A 
  reflexivity proved by (Relation_Definitions.equiv_refl A eq_A eq_proof)
    symmetry proved by (Relation_Definitions.equiv_sym A eq_A eq_proof)
      transitivity proved by (Relation_Definitions.equiv_trans _ _ eq_proof) as EQA.

End Convert.

Lemma beq_nat_ok : forall n1 n2, if beq_nat n1 n2 then n1 = n2 else n1 <> n2.
Proof.
fix 1; intros [ | n1] [ | n2]; simpl; try reflexivity; try discriminate.
generalize (beq_nat_ok n1 n2); case (beq_nat n1 n2); [intro; subst; reflexivity | intros n1_diff_n2 H; apply n1_diff_n2; injection H; intro; assumption].
Defined.
