(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha & Frederic Blanqui, 2010-05-04

Dependency relation on defined symbols implied by rules:

f is bigger than g if g occurs in the RHS of a defining rule of f
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs ListUtil ACalls LogicUtil RelMidex VecUtil.
From Stdlib Require Import Relations Bool.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** defined symbols occuring in a term *)

(*IMPROVE:
1) merge filter and symbs into a single function
2) define once and for all the list of defined symbols,
3) define defined symbols as set, assuming a total ordering on symbols?
*)

  Definition def_symbs R (t : term) := filter (fun f => defined f R) (symbs t).

  Lemma def_symbs_incl : forall R a t, def_symbs R t [= def_symbs (a :: R) t.

  Proof.
    intros. intro x; unfold def_symbs. rewrite !filter_In; simpl.
    destruct a as [[] r]; simpl; auto. rewrite orb_true_iff.
    intro H. destruct H; split; auto.
  Qed.

(***********************************************************************)
(** function testing if the root of a term is equal to some given symbol *)

  Definition root_eq (f : Sig) (t : term) : bool :=
    match t with | Fun g _ => beq_symb f g | _ => false end.

(***********************************************************************)
(** dependency relation on defined symbols implied by rules *)

(*IMPROVE:
1) replace (In g (def_symbs R (rhs a)))
by (In g (symbs (rhs a)) /\ defined R g = true)
2) replace (In g (symbs (rhs a)))
by a function testing whether a symbol occurs in a term
*)

  Definition symb_ord R : relation Sig := fun f g =>
    exists a, In a R /\ root_eq f (lhs a) = true /\ In g (def_symbs R (rhs a)).

  Lemma symb_ord_cons : forall a R f g, symb_ord R f g -> symb_ord (a :: R) f g.

  Proof.
    intros. destruct H as [h [Hh1 [Hh2 Hh3]]]. exists h. split.
    apply in_cons; auto.
    split; auto. unfold def_symbs; simpl. destruct a as [[] r]; simpl; auto.
    unfold def_symbs in Hh3; rewrite filter_In in Hh3; rewrite filter_In.
    split; destruct Hh3; auto. rewrite orb_true_iff, H0; right; auto.
  Qed.

  Lemma symb_ord_cons_var : forall R f g n r,
    symb_ord (mkRule (Var n) r :: R) f g -> symb_ord R f g.

  Proof.
    intros.
    destruct H as [x [H [H1 H2]]].
    destruct (in_inv H).
    rewrite <-H0 in H1; simpl in H1; inversion H1.
    exists x; split; auto.
  Qed.

  Fixpoint symb_ord_img_rec R Rc f : list Sig := 
    match Rc with
      | nil => nil
      | a :: Rc' =>
        if root_eq f (lhs a) && Inb (@eq_rule_dec Sig) a R then
          def_symbs R (rhs a) ++ symb_ord_img_rec R Rc' f
          else symb_ord_img_rec R Rc' f
    end.

  Lemma symb_ord_img_rec_cons1 : forall Rc a R f,
    symb_ord_img_rec R Rc f [= symb_ord_img_rec (a :: R) Rc f.

  Proof.
    intro Rc; elim Rc; simpl; intros. refl.
    destruct (eq_rule_dec a a0).
    case_eq (root_eq f (lhs a)); intro H0; simpl.
    case_eq (Inb (@eq_rule_dec _) a R); intro H1.
    apply app_incl. apply def_symbs_incl. apply H.
    apply incl_appr; apply H.
    apply H.
    case_eq (root_eq f (lhs a) && Inb (@eq_rule_dec _) a R); intro H0.
    apply app_incl. apply def_symbs_incl. apply H.
    apply H.
  Qed.

  Lemma symb_ord_img_rec_cons2 : forall Rc a R f,
    symb_ord_img_rec R Rc f [= symb_ord_img_rec R (a :: Rc) f.

  Proof.
    intros; simpl.
    case_eq (root_eq f (lhs a) && Inb (@eq_rule_dec _) a R); intro H.
    apply incl_appr; refl. refl.
  Qed.

  Lemma symb_ord_img_recP1 : forall Rc R f g,
    In g (symb_ord_img_rec R Rc f) -> symb_ord R f g.

  Proof.
    intro Rc; elim Rc; simpl; intros; try tauto.
    case_eq (root_eq f (lhs a) && Inb (@eq_rule_dec _) a R); intro H1;
      rewrite H1 in H0.
    2: apply (H R f g H0).
    rewrite andb_true_iff in H1; destruct H1. destruct (in_app_or H0).
    exists a; split; auto. apply (Inb_true (@eq_rule_dec _) _ _ H2).
    apply (H R f g H3).
  Qed.

  Lemma symb_ord_img_recP2 : forall Rc R f g a,
    In g (def_symbs R (rhs a)) -> In a R -> In a Rc ->
    root_eq f (lhs a) = true -> In g (symb_ord_img_rec R Rc f).

  Proof.
    intro Rc; elim Rc; intros. inversion H1.
    destruct (in_inv H2).
    simpl. subst. rewrite H3, (Inb_intro (@eq_rule_dec _) _ _ H1). simpl.
    apply in_appl; auto.
    apply symb_ord_img_rec_cons2. apply (H R f g a0); auto.
  Qed.

  Lemma symb_ord_img_rec_incl : forall Rc1 Rc2 R f,
    Rc1 [= Rc2 -> symb_ord_img_rec R Rc1 f [= symb_ord_img_rec R Rc2 f.

  Proof.
    intros Rc1. induction Rc1.
    simpl; intros. apply incl_nil.
    intros. simpl.
    case_eq (root_eq f (lhs a) && Inb (@eq_rule_dec _) a R); intro H0.
    2:{apply IHRc1. apply incl_cons_l_incl with (x := a); auto. }
    apply incl_app. intros g Hg. rewrite andb_true_iff in H0. destruct H0.
    apply symb_ord_img_recP2 with (a := a); auto.
    apply (Inb_true (@eq_rule_dec _) _ _ H1). apply (incl_cons_l_in H).
    apply IHRc1. apply incl_cons_l_incl with (x := a); auto.
  Qed.

  Lemma symb_ord_img_incl : forall Rc R f g,
    R [= Rc -> symb_ord R f g -> In g (symb_ord_img_rec R Rc f).

  Proof.
    intros. apply symb_ord_img_rec_incl with (Rc1 := R); auto.
    destruct H0 as [a [H0 [H1 H2]]]. apply symb_ord_img_recP2 with (a := a);
      auto.
  Qed.

  Definition symb_ord_img R f := symb_ord_img_rec R R f.

  Lemma symb_ord_imgP : forall R f g,
    In g (symb_ord_img R f) <-> symb_ord R f g.

  Proof.
    unfold symb_ord_img; intros; split.
    apply symb_ord_img_recP1.
    intros. destruct H as [a [H0 [H1 H2]]].
    apply (symb_ord_img_recP2 R R f g a); auto.
  Qed.

  Lemma symb_ord_dec : forall R, rel_dec (symb_ord R).

  Proof.
    intros R a b.
    case_eq (Inb (@eq_symb_dec _) b (symb_ord_img R a)); intro H.
    left. rewrite <- symb_ord_imgP. apply (Inb_true (@eq_symb_dec _) _ _ H).
    right. intro. rewrite  <- symb_ord_imgP in H0.
    apply (Inb_false (@eq_symb_dec _) _ _ H); auto.
  Qed.

(***********************************************************************)
(** LHS root symbols of a list of rules *)

  Fixpoint root_lhs_rules (R : rules) : list Sig :=
    match R with
      | nil => nil
      | a :: R' =>
        match lhs a with
          | Fun f _ => f :: root_lhs_rules R'
          | _ => root_lhs_rules R'
        end
    end.

  Lemma root_lhsP : forall R f,
    In f (root_lhs_rules R) <-> exists a, In a R /\ root_eq f (lhs a) = true.

  Proof.
    induction R; simpl.
    intro. split; try tauto. intro. destruct H as [a [H _]]; auto.
    intro. destruct a as [[n| F vs] r]; simpl.
    split; intro. destruct (proj1 (IHR f) H) as [a [H0 H1]].
    exists a; split; auto.
    destruct H as [a [H0 H1]]. destruct H0.
    destruct a as [[n' | F vs] r']. simpl in H1. inversion H1. inversion H.
    apply (IHR f). exists a; auto.
    split; intro. destruct H.
    exists (mkRule (Fun F vs) r). split. left; auto. simpl.
    rewrite H, beq_symb_ok; auto.
    destruct (proj1 (IHR f) H) as [a [H0 H1]]. exists a; split; auto.
    destruct H as [a [H H0]]. destruct H.
    destruct a as [[n | F' vs'] r']. inversion H0. inversion H. simpl in H0.
    rewrite <- H2, beq_symb_ok in H0; auto.
    right. apply (IHR f). exists a; auto.
  Qed.

End S.
