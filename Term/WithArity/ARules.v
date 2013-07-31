(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-24

infinite sets of rules
*)

Set Implicit Arguments.

Require Import ATrs ListUtil RelUtil ARelation LogicUtil SetUtil Syntax.

Section defs.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation rule := (rule Sig).

  Definition rules := set rule.

(***********************************************************************)
(** finite rewriting *)

  Definition Rules R : rules := fun x => In x R.

  Lemma Rules_cons : forall a R, Rules (a :: R) [=] a :: Rules R.

  Proof. unfold Rules. simpl. split. intuition. subst. fo. fo. fo. Qed.

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

Require Import Morphisms.

Instance red_incl Sig : Proper (incl ==> inclusion) (@red Sig).

Proof. intros R R' RR' t t' tt'. redtac. exists l r c s. fo. Qed.

Instance hd_red_incl Sig : Proper (incl ==> inclusion) (@hd_red Sig).

Proof. intros R R' RR' t t' tt'. redtac. exists l r s. fo. Qed.

Instance red_mod_incl Sig : Proper (incl ==> incl ==> inclusion) (@red_mod Sig).

Proof. intros E E' EE' R R' RR'. unfold red_mod. rewrite EE', RR'. refl. Qed.

Instance hd_red_mod_incl Sig :
  Proper (incl ==> incl ==> inclusion) (@hd_red_mod Sig).

Proof. intros E E' EE' R R' RR'. unfold hd_red_mod. rewrite EE', RR'. refl. Qed.

(***********************************************************************)
(** properties of rewriting *)

Section props.

  Variable Sig : Signature.

  Notation rule := (rule Sig). Notation rules := (set rule).
  Notation Rules := (@Rules Sig).

  Lemma red_rule : forall (R : rules) l r c s, R (mkRule l r) ->
    red R (fill c (sub s l)) (fill c (sub s r)).

  Proof. intros. unfold red. exists l. exists r. exists c. exists s. auto. Qed.

  Lemma hd_red_rule : forall (R : rules) l r s, R (mkRule l r) ->
    hd_red R (sub s l) (sub s r).

  Proof. intros. unfold hd_red. exists l. exists r. exists s. auto. Qed.

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

  Lemma rt_red_empty : red (@empty rule) # == eq.

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
    eapply inclusion_elim. apply clos_refl_trans_inclusion. apply red_incl.
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

  Lemma red_mod_empty : forall R : rules, red_mod (@empty rule) R == red R.

  Proof.
    intro. unfold red_mod. rewrite rt_red_empty. split; intros t u h.
    destruct h. intuition. subst. hyp. exists t. auto.
  Qed.

End props.
