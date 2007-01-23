(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

rewriting
*)

(* $Id: ATrs.v,v 1.7 2007-01-23 16:42:56 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

(***********************************************************************)
(** rule *)

Record rule : Set := mkRule {
  lhs : term;
  rhs : term
}.

Notation rules := (list rule).

(***********************************************************************)
(** rewrite step *)

Section rewriting.

Variable R : rules.

Require Export ASubstitution.

Definition red (t1 t2 : term) :=
  exists l, exists r, exists c, exists s,
  In (mkRule l r) R /\ t1 = fill c (app s l) /\ t2 = fill c (app s r).

Definition hd_red (t1 t2 : term) :=
  exists l, exists r, exists s,
  In (mkRule l r) R /\ t1 = app s l /\ t2 = app s r.

Definition int_red (t1 t2 : term) :=
  exists l, exists r, exists c, exists s, c <> Hole
  /\ In (mkRule l r) R /\ t1 = fill c (app s l) /\ t2 = fill c (app s r).

Ltac redtac := repeat
  match goal with
    | H : red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp red _ _ |- _ =>
      unfold transp in H; redtac
    | H : hd_red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp hd_red _ _ |- _ =>
      unfold transp in H; redtac
    | H : int_red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp int_red _ _ |- _ =>
      unfold transp in H; redtac
  end.

Lemma red_rule : forall l r c s, In (mkRule l r) R ->
  red (fill c (app s l)) (fill c (app s r)).

Proof.
intros. unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma red_rule_top : forall l r s, In (mkRule l r) R ->
  red (app s l) (app s r).

Proof.
intros. unfold red. exists l. exists r. exists (@Hole Sig). exists s. auto.
Qed.

Lemma hd_red_rule : forall l r s, In (mkRule l r) R ->
  hd_red (app s l) (app s r).

Proof.
intros. unfold hd_red. exists l. exists r. exists s. auto.
Qed.

Lemma red_fill : forall c t u, red t u -> red (fill c t) (fill c u).

Proof.
intros. redtac. unfold red.
exists l. exists r. exists (AContext.comp c c0). exists s. split. assumption.
subst t. subst u. do 2 rewrite fill_comp. auto.
Qed.

Lemma red_subterm : forall u u' t, red u u' -> subterm_eq u t
  -> exists t', red t t' /\ subterm_eq u' t'.

Proof.
unfold subterm_eq. intros. destruct H0 as [d]. subst t. redtac. subst u.
subst u'.
exists (fill (AContext.comp d c) (app s r)). split.
exists l. exists r. exists (AContext.comp d c). exists s. split. assumption.
rewrite fill_comp. auto. exists d. rewrite fill_comp. refl.
Qed.

Lemma int_red_fun : forall f ts v, int_red (Fun f ts) v
  -> exists i, exists vi : terms i, exists t, exists j, exists vj : terms j,
    exists h, exists t', ts = Vcast (Vapp vi (Vcons t vj)) h
    /\ v = Fun f (Vcast (Vapp vi (Vcons t' vj)) h) /\ red t t'.

Proof.
intros. redtac. destruct c. absurd (@Hole Sig = Hole); auto. clear H.
simpl in H1.
Funeqtac. exists i. exists v0. exists (fill c (app s l)). exists j. exists v1.
exists e. exists (fill c (app s r)). split. assumption. split. assumption.
unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Require Export RelUtil.

Lemma int_red_incl_red : int_red << red.

Proof.
unfold inclusion, int_red. intros. decomp H. subst x. subst y. apply red_rule.
assumption.
Qed.

Lemma hd_red_incl_red : hd_red << red.

Proof.
unfold inclusion. intros. redtac. subst x. subst y. apply red_rule_top. exact H.
Qed.

(***********************************************************************)
(** preservation of variables under reduction *)

Section variables.

Variable hyp : forall a, In a R -> incl (vars (rhs a)) (vars (lhs a)).

Lemma vars_preserved : forall t u, red t u -> incl (vars u) (vars t).

Proof.
intros. redtac. subst t. subst u.
Abort.

End variables.

(***********************************************************************)
(** rewriting vectors of terms *)

Require Export VecOrd.

Definition terms_gt := Vgt_prod red.

Lemma Vgt_prod_fun : forall f ts ts',
  Vgt_prod red ts ts' -> int_red (Fun f ts) (Fun f ts').

Proof.
intros. deduce (Vgt_prod_gt H). do 8 destruct H0. destruct H1. redtac.
subst x1. subst x5. unfold transp, int_red. rewrite H0. rewrite H1.
exists l. exists r. exists (Cont f x4 x0 c x3). exists s. split. discriminate.
auto.
Qed.

End rewriting.

(***********************************************************************)
(** rewriting modulo *)

Section rewriting_modulo.

Variable E R : rules.

Definition red_mod := red E # @ red R.

Definition hd_red_mod := red E # @ hd_red R.

Lemma hd_red_mod_incl_red_mod : hd_red_mod << red_mod.

Proof.
unfold hd_red_mod, red_mod. comp. apply hd_red_incl_red.
Qed.

End rewriting_modulo.

End S.

(***********************************************************************)
(** declarations of implicit arguments *)

Implicit Arguments int_red_fun [Sig R f ts v].

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (red _) _ _ |- _ =>
      unfold transp in H; redtac
    | H : hd_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (hd_red _) _ _ |- _ =>
      unfold transp in H; redtac
    | H : int_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp (int_red _) _ _ |- _ =>
      unfold transp in H; redtac
  end.