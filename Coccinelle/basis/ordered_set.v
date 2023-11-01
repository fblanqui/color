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

From Coq Require Import Setoid Relations Arith FunInd.

Inductive comp : Type :=
  | Equivalent : comp
  | Less_than : comp
  | Greater_than : comp
  | Uncomparable : comp.

Module Type S.

Parameter A : Type.
Parameter eq_bool : A -> A -> bool.
Parameter eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => a1 = a2 | false => ~ a1 = a2 end.

Parameter o : relation A.
Parameter o_bool : A -> A -> bool.
Parameter o_bool_ok : forall a1 a2, match o_bool a1 a2 with true => o a1 a2 | false => ~ o a1 a2 end.
Parameter o_proof : order A o.
Parameter o_total : forall e1 e2 : A, {o e1 e2} + {o e2 e1}.

End S.

Module Type ES.

Parameter A : Type.
Parameter eq_A : relation A.
Parameter eq_bool : A -> A -> bool.
Parameter eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => eq_A a1 a2 | false => ~eq_A a1 a2 end.
Parameter eq_proof : equivalence A eq_A.

Parameter o : relation A.
Parameter o_compat : 
  forall e1 e1' e2 e2', eq_A e1 e1' -> eq_A e2 e2' -> o e1 e2 -> o e1' e2'.
Parameter o_bool : A -> A -> bool.
Parameter o_bool_ok : forall a1 a2, match o_bool a1 a2 with true => o a1 a2 | false => ~ o a1 a2 end.
Parameter o_proof : order A o.
Parameter o_total : forall e1 e2 : A, {o e1 e2} + {o e2 e1}.

  Add Relation A eq_A 
  reflexivity proved by (equiv_refl _ _ eq_proof)
    symmetry proved by (equiv_sym _ _ eq_proof)
      transitivity proved by (equiv_trans _ _ eq_proof) as EQA.

End ES.

(*
Lemma toto : forall (A : Type) (R : relation A),
  (order A R) ->
  (forall e1 e2 : A, {R e1 e2} + {~ R e1 e2}) ->
  (forall e1 e2 : A, {R e1 e2} + {R e2 e1}) ->
  forall e1 e2 : A, {e1 = e2} + {e1 <> e2}.
Proof.
intros A R Ord Dec Tot e1 e2; destruct Ord.
destruct (Tot e1 e2) as [e1_le_e2 | e2_le_e1].
destruct (Dec e2 e1) as [e2_le_e1 | not_e2_le_e1].
left; apply ord_antisym; trivial.
right; intro; apply not_e2_le_e1; subst; trivial.
destruct (Dec e1 e2) as [e1_le_e2 | not_e1_le_e2].
left; apply ord_antisym; trivial.
right; intro; apply not_e1_le_e2; subst; trivial.
Qed.
*)

Module Nat <: S with Definition A:=nat.

Definition A := nat.
Definition o : relation A := le.

Lemma o_proof : order A o.
Proof.
unfold o; constructor; auto.
unfold reflexive; auto.
unfold transitive; intros n1 n2 n3 H1 H2; apply Nat.le_trans with n2; trivial.
unfold antisymmetric; auto with arith.
Qed.

Lemma o_dec : forall e1 e2 : A, {o e1 e2} + {~ o e1 e2}.
Proof.
unfold o.
induction e1; induction e2.
left; trivial.
left; auto with arith.
right; auto with arith.
destruct (IHe1 e2); destruct IHe2; auto with arith.
Defined.

Function eq_bool (n m : nat) {struct n} : bool :=
  match n, m with
  | O, O => true
  | (S n'), (S m') => eq_bool n' m'
  | _,  _ => false
  end.

Lemma eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => a1 = a2 | false => ~a1 = a2 end.
fix eq_bool_ok 1.
intros [ | n] [ | m]; simpl.
reflexivity.
discriminate.
discriminate.
generalize (eq_bool_ok n m); case (eq_bool n m).
intros; subst; reflexivity.
intros n_diff_m Sn_eq_Sm; apply n_diff_m; injection Sn_eq_Sm; intro; assumption.
Defined.

Function o_bool (n m : nat) {struct n} : bool :=
  match n, m with
  | O, _ => true
  | (S n'), (S m') => o_bool n' m'
  | (S n'),  O => false
  end.

Lemma o_bool_ok : forall a1 a2, match o_bool a1 a2 with true => o a1 a2 | false => ~ o a1 a2 end.
unfold o; fix o_bool_ok 1.
intros [ | n] [ | m]; simpl.
apply le_n.
apply Nat.le_0_l.
intro H; inversion H.
generalize (o_bool_ok n m); case (o_bool n m).
intro H; apply (le_n_S _ _ H).
intros H H'; apply H; apply (le_S_n _ _ H').
Defined.

Lemma o_total : forall e1 e2 : A, {o e1 e2} + {o e2 e1}.
Proof.
intros.
unfold o.
change ({e1<=e2}+{e1>=e2}).
apply le_ge_dec.
Qed.

End Nat.

