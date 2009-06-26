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
Require Import SetUtil.

Section defs.

Variable Sig : Signature.

Notation term := (term Sig). Notation rule := (rule Sig).

Definition rules := set rule.

(***********************************************************************)
(** (finite) set of rules from a list of rules *)

Definition Rules R : rules := fun x => In x R.

(***********************************************************************)
(** rewriting *)

Definition red (R : rules) : relation term :=
  fun u v => exists l, exists r, exists c, exists s,
    R (mkRule l r) /\ u = fill c (sub s l) /\ v = fill c (sub s r).

Definition hd_red (R : rules) : relation term :=
  fun u v => exists l, exists r, exists s,
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
(** monotony properties *)

Require Import Setoid.

Add Parametric Morphism (Sig : Signature) : (@red Sig)
  with signature (@incl (@rule Sig)) ==> (@inclusion (term Sig))
    as red_incl.

Proof.
intros R R' RR' u v Rst. redtac.
exists l. exists r. exists c. exists s. repeat split; try hyp.
apply RR'. hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@red Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==> (same_relation (term Sig))
    as red_equiv.

Proof.
intros R S. rewrite equiv_elim. intros [h1 h2]. split; apply red_incl; hyp.
Qed.

(*COQ: can be remobed?*)
Add Parametric Morphism (Sig : Signature) : (@red Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==>
    (@eq (term Sig)) ==> (@eq (term Sig)) ==> iff
    as red_equiv_ext.

Proof.
intros A B. rewrite equiv_elim. intros [h1 h2]. split; apply red_incl; hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@hd_red Sig)
  with signature (@incl (@rule Sig)) ==> (@inclusion (term Sig))
    as hd_red_incl.

Proof.
intros R R' RR' u v Rst. redtac.
exists l. exists r. exists s. repeat split; try hyp.
apply RR'. hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@hd_red Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==> (same_relation (term Sig))
    as hd_red_equiv.

Proof.
intros R S. rewrite equiv_elim. intros [h1 h2]. split; apply hd_red_incl; hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@hd_red Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==>
    (@eq (term Sig)) ==> (@eq (term Sig)) ==> iff
    as hd_red_equiv_ext.

Proof.
intros R S. rewrite equiv_elim. intros [h1 h2]. split; apply hd_red_incl; hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@red_mod Sig)
  with signature (@incl (@rule Sig)) ==>
    (@incl (@rule Sig)) ==> (@inclusion (term Sig))
    as red_mod_incl.

Proof.
intros. unfold red_mod. comp. apply incl_rtc.
apply red_incl. hyp. apply red_incl. hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@red_mod Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==>
    (@SetUtil.equiv (@rule Sig)) ==> (same_relation (term Sig))
    as red_mod_equiv.

Proof.
intros R R'. rewrite equiv_elim. intros [h1 h2].
intros S S'. rewrite equiv_elim. intros [h3 h4].
split; apply red_mod_incl; hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@red_mod Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==>
    (@SetUtil.equiv (@rule Sig)) ==>
    (@eq (term Sig)) ==> (@eq (term Sig)) ==> iff
    as red_mod_equiv_ext.

Proof.
intros R R'. rewrite equiv_elim. intros [h1 h2].
intros S S'. rewrite equiv_elim. intros [h3 h4].
split; apply red_mod_incl; hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@hd_red_mod Sig)
  with signature (@incl (@rule Sig)) ==>
    (@incl (@rule Sig)) ==> (@inclusion (term Sig))
    as hd_red_mod_incl.

Proof.
intros. unfold hd_red_mod. comp. apply incl_rtc. apply red_incl. hyp.
apply hd_red_incl. hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@hd_red_mod Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==>
    (@SetUtil.equiv (@rule Sig)) ==> (same_relation (term Sig))
    as hd_red_mod_equiv.

Proof.
intros R R'. rewrite equiv_elim. intros [h1 h2].
intros S S'. rewrite equiv_elim. intros [h3 h4].
split; apply hd_red_mod_incl; hyp.
Qed.

Add Parametric Morphism (Sig : Signature) : (@hd_red_mod Sig)
  with signature (@SetUtil.equiv (@rule Sig)) ==>
    (@SetUtil.equiv (@rule Sig)) ==>
    (@eq (term Sig)) ==> (@eq (term Sig)) ==> iff
    as hd_red_mod_equiv_ext.

Proof.
intros R R'. rewrite equiv_elim. intros [h1 h2].
intros S S'. rewrite equiv_elim. intros [h3 h4].
split; apply hd_red_mod_incl; hyp.
Qed.

(***********************************************************************)
(** properties of rewriting *)

Section props.

Variable Sig : Signature.

Notation rule := (rule Sig). Notation rules := (set rule).

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

End red.

Section red_mod.

Variables E E' R R' : rules.

Lemma context_closed_red_mod : context_closed (red_mod E R).

Proof.
apply context_closed_comp. apply context_closed_rtc. apply context_closed_red.
apply context_closed_red.
Qed.

Lemma red_mod_union : red_mod E R << red (E ++ R) #.

Proof.
intros t u [h [h1 h2]]. gen h2. gen h1. induction 1; intro.
apply rt_trans with y.
apply rt_step. apply red_incl with E. apply incl_appl. hyp.
apply rt_step. apply red_incl with R. apply incl_appr. hyp.
apply rt_step. apply red_incl with R. apply incl_appr. hyp.
apply rt_trans with y.
eapply inclusion_elim. apply incl_rtc. apply red_incl. apply incl_appl. hyp.
auto.
Qed.

Lemma rt_red_mod_union : red_mod E R # << red (E ++ R) #.

Proof.
trans (red(E++R)##). rewrite red_mod_union. refl. rewrite rtc_invol. refl.
Qed.

End red_mod.

End props.
