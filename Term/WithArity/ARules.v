(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-24

infinite sets of rules
*)

Set Implicit Arguments.

Require Import ATrs ListUtil RelUtil ARelation LogicUtil SetUtil.

Section defs.

Variable Sig : Signature.

Notation term := (term Sig). Notation rule := (rule Sig).

Definition rules := set rule.

(***********************************************************************)
(** finite rewriting *)

Definition Rules R : rules := fun x => In x R.

Lemma Rules_cons : forall a R, Rules (a :: R) [=] a :: Rules R.

Proof.
unfold Rules. simpl. split. intuition. subst. fo. fo.
fo.
Qed.

Lemma Rules_app : forall R S, Rules (R ++ S) [=] Rules R ++ Rules S.

Proof.
split; unfold Rules, union; intro. rewrite in_app in H. hyp. destruct H.
apply in_appl. hyp. apply in_appr. hyp.
Qed.

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

(*COQ: can be removed?*)
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
intros. unfold red_mod. comp. apply clos_refl_trans_m'.
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
intros. unfold hd_red_mod. comp. apply clos_refl_trans_m'. apply red_incl. hyp.
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
Notation Rules := (@Rules Sig). Notation empty := (@empty rule).

Lemma red_rule : forall (R : rules) l r c s, R (mkRule l r) ->
  red R (fill c (sub s l)) (fill c (sub s r)).

Proof.
intros. unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma hd_red_rule : forall (R : rules) l r s, R (mkRule l r) ->
  hd_red R (sub s l) (sub s r).

Proof.
intros. unfold hd_red. exists l. exists r. exists s. auto.
Qed.

Lemma context_closed_red : forall R : rules, context_closed (red R).

Proof.
intros R t u c h. redtac. subst. repeat rewrite fill_fill.
exists l. exists r. exists (comp c c0). exists s. intuition.
Qed.

Lemma red_Rules : forall R, red (Rules R) == ATrs.red R.

Proof.
split; intros t u H. redtac. subst. apply ATrs.red_rule. hyp.
ATrs.redtac. subst. apply red_rule. hyp.
Qed.

Lemma hd_red_Rules : forall R, hd_red (Rules R) == ATrs.hd_red R.

Proof.
split; intros t u H. redtac. subst. apply ATrs.hd_red_rule. hyp.
ATrs.redtac. subst. apply hd_red_rule. hyp.
Qed.

Lemma rt_red_empty : red empty # == @eq (@term Sig).

Proof.
split; intros t u h. elim h; intros. redtac. contr. refl.
trans y; hyp. subst. apply rt_refl.
Qed.

(***********************************************************************)
(** properties of rewriting modulo *)

Lemma context_closed_red_mod : forall E R : rules,
  context_closed (red_mod E R).

Proof.
intros. apply context_closed_comp. apply context_closed_rtc.
apply context_closed_red. apply context_closed_red.
Qed.

Lemma red_mod_union : forall E R : rules, red_mod E R << red (E ++ R) #.

Proof.
intros E R t u [h [h1 h2]]. revert h1 h2. induction 1; intro.
apply rt_trans with y.
apply rt_step. apply red_incl with E. apply incl_appl. hyp.
apply rt_step. apply red_incl with R. apply incl_appr. hyp.
apply rt_step. apply red_incl with R. apply incl_appr. hyp.
apply rt_trans with y.
eapply inclusion_elim. apply clos_refl_trans_m'. apply red_incl.
apply incl_appl. hyp.
auto.
Qed.

Lemma rt_red_mod_union : forall E R : rules, red_mod E R # << red (E ++ R) #.

Proof.
intros. incl_trans (red(E++R)##). rewrite red_mod_union. refl.
rewrite rtc_invol. refl.
Qed.

Lemma red_mod_Rules : forall E R,
  red_mod (Rules E) (Rules R) == ATrs.red_mod E R.

Proof.
intros. unfold red_mod, ATrs.red_mod. repeat rewrite red_Rules. refl.
Qed.

Lemma hd_red_mod_Rules : forall E R,
  hd_red_mod (Rules E) (Rules R) == ATrs.hd_red_mod E R.

Proof.
intros. unfold hd_red_mod, ATrs.hd_red_mod. repeat rewrite red_Rules.
repeat rewrite hd_red_Rules. refl.
Qed.

Lemma red_mod_empty : forall R : rules, red_mod empty R == red R.

Proof.
intro. unfold red_mod. rewrite rt_red_empty. split; intros t u h.
destruct h. intuition. subst. hyp. exists t. auto.
Qed.

End props.
