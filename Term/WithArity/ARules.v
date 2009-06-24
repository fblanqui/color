(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-24

infinite sets of rules
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import List.
Require Import RelUtil.
Require Import ARelation.
Require Import LogicUtil.

Section defs.

Variable Sig : Signature.

Notation rule := (rule Sig).

(***********************************************************************)
(** infinite sets of rules *)

Definition rules := rule -> Prop.

Definition Empty (x : rule) := False.

Definition Rules R (x : rule) := In x R.

Definition incl R S := forall x : rule, R x -> S x.

Definition union R S := fun x : rule => R x \/ S x.

Infix "++" := union.

(***********************************************************************)
(** rewriting *)

Definition red (R : rules) u v := exists l, exists r, exists c, exists s,
    R (mkRule l r) /\ u = fill c (sub s l) /\ v = fill c (sub s r).

Definition hd_red (R : rules) u v := exists l, exists r, exists s,
    R (mkRule l r) /\ u = sub s l /\ v = sub s r.

Definition red_mod E R := red E # @ red R.

Definition hd_red_mod E R := red E # @ hd_red R.

End defs.

Ltac redtac := repeat
  match goal with
    | H : red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in 
      let c := fresh "c" in let s := fresh "s" in 
      let lr := fresh "lr" in let xl := fresh "xl" in
      let yr := fresh "yr" in
        destruct H as [l [r [c [s [lr [xl yr]]]]]]
    | H : transp (red _) _ _ |- _ => unfold transp in H; redtac
    | H : hd_red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let lr := fresh "lr" in 
      let xl := fresh "xl" in let yr := fresh "yr" in
        destruct H as [l [r [s [lr [xl yr]]]]]
    | H : transp (hd_red _) _ _ |- _ => unfold transp in H; redtac
    | H : red_mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        destruct H as [t h]; destruct h; redtac
    | H : hd_red_mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        destruct H as [t h]; destruct h; redtac
  end.

(***********************************************************************)
(** properties of rules *)

Section props.

Variable Sig : Signature.

Notation rules := (rules Sig).

Lemma incl_refl : forall R : rules, incl R R.

Proof.
intros R x. auto.
Qed.

(***********************************************************************)
(** properties of rewriting *)

Section red.

Variable R R' : rules.

Lemma red_rule : forall l r c s, R (mkRule l r) ->
  red R (fill c (sub s l)) (fill c (sub s r)).

Proof.
intros. unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma hd_red_rule : forall l r s, R (mkRule l r) ->
  hd_red R (sub s l) (sub s r).

Proof.
intros. unfold hd_red. exists l. exists r. exists s. auto.
Qed.

Lemma context_closed_red : context_closed (red R).

Proof.
intros t u c h. redtac. subst. repeat rewrite fill_fill.
exists l. exists r. exists (comp c c0). exists s. intuition.
Qed.

Lemma red_incl : incl R R' -> red R << red R'.

Proof.
intros RR' u v Rst. redtac.
exists l. exists r. exists c. exists s. repeat split; try assumption.
apply RR'. assumption.
Qed.

Lemma hd_red_incl : incl R R' -> hd_red R << hd_red R'.

Proof.
intros RR' u v Rst. redtac.
exists l. exists r. exists s. repeat split; try assumption.
apply RR'. assumption.
Qed.

End red.

Section red_mod.

Variables E E' R R' : rules.

Lemma context_closed_red_mod : context_closed (red_mod E R).

Proof.
apply context_closed_comp. apply context_closed_rtc. apply context_closed_red.
apply context_closed_red.
Qed.

Lemma red_mod_incl : incl R R' -> incl E E' -> red_mod E R << red_mod E' R'.

Proof.
intros. unfold red_mod. comp. apply incl_rtc.
apply red_incl. hyp. apply red_incl. hyp.
Qed.

Lemma hd_red_mod_incl :
  incl E E' -> incl R R' -> hd_red_mod E R << hd_red_mod E' R'.

Proof.
intros. unfold hd_red_mod. comp. apply incl_rtc. apply red_incl. hyp.
apply hd_red_incl. hyp.
Qed.

End red_mod.

End props.
