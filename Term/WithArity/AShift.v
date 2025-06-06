(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-22

term variables shifting
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil ATrs RelUtil ListUtil VecUtil VecMax
  NatUtil ASubstitution.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation vars := (@vars Sig).

  Notation rule := (rule Sig). Notation rules := (list rule).
  Notation lhs := (@lhs Sig).

(***********************************************************************)
(** shift variable indices in terms *)

  Section shift.

    Variable p : nat.

    Definition shift_var x := x+p.

    Definition shift_sub x := @Var Sig (x+p).
    Definition shift := sub shift_sub.

    Definition shift_rule (rho : rule) :=
      let (l,r) := rho in mkRule (shift l) (shift r).

(***********************************************************************)
(** properties of shifting *)

    Lemma in_vars_shift_min x t : In x (vars (shift t)) -> p <= x.

    Proof.
      pattern t. apply term_ind_forall; clear t.
      simpl. intros. destruct H. lia. contr.
      intros. unfold shift in H0. rewrite sub_fun, vars_fun in H0.
      ded (in_vars_vec_elim H0). do 2 destruct H1.
      ded (Vin_map H1). do 2 destruct H3. subst x0.
      ded (Vforall_in H H3). auto.
    Qed.

    Lemma in_vars_shift_max x t : In x (vars (shift t)) -> x <= maxvar t + p.

    Proof.
      pattern t. apply term_ind_forall; clear t.
      simpl. intros. destruct H. lia. contr.
      intros. unfold shift in H0. rewrite sub_fun, vars_fun in H0.
      ded (in_vars_vec_elim H0). do 2 destruct H1.
      ded (Vin_map H1). do 2 destruct H3. subst x0.
      ded (Vforall_in H H3). ded (H4 H2).
      rewrite maxvar_fun. ded (Vin_map_intro (f:=@maxvar Sig) H3).
      ded (Vmax_in H6). unfold maxvars. lia.
    Qed.

    Lemma vars_shift : forall t, vars (shift t) = map shift_var (vars t).

    Proof.
      apply term_ind with (Q := fun n (v : terms n) =>
        vars_vec (Vmap shift v) = map shift_var (vars_vec v)); intros. refl.
      unfold shift. rewrite sub_fun, !vars_fun. exact H.
      refl. simpl. rewrite map_app, H. apply appr_eq. exact H0.
    Qed.

    Lemma notin_vars_shift x l :
      ~In x (vars (shift l)) -> p <= x -> ~In (x-p) (vars l).

    Proof.
      intros h1 h2 h3. apply h1. rewrite vars_shift, <- (le_minus_plus h2).
      fold (shift_var (x-p)). apply in_map. hyp.
    Qed.

(***********************************************************************)
(** inverse shifting wrt a term *)

    Section inverse.

      Variable l : term.

      Definition shift_inv_var x :=
        match le_lt_dec p x with
        | left _ => (* p <= x *)
          if Inb eq_nat_dec (x-p) (vars l) then x-p else x
        | right _ => (* p > x *) x
        end.

      Definition shift_inv_sub x := @Var Sig (shift_inv_var x).
      Definition shift_inv := sub shift_inv_sub.

      Lemma sub_shift s : sub s l = sub (sub_comp s shift_inv_sub) (shift l).

      Proof.
        unfold shift. rewrite sub_sub. apply sub_eq. intros.
        rewrite sub_comp_assoc. unfold sub_comp. simpl. f_equal.
        unfold shift_inv_var. rewrite plus_minus_eq.
        assert (Inb eq_nat_dec x (vars l) = true). apply Inb_intro. exact H.
        rewrite H0. case (le_lt_dec p (x+p)); intro. refl. lia.
      Qed.

      Lemma sub_shift_incl s r : vars r [= vars l ->
        sub s r = sub (sub_comp s shift_inv_sub) (shift r).

      Proof.
        intro. unfold shift. rewrite sub_sub. apply sub_eq. intros.
        rewrite sub_comp_assoc. unfold sub_comp. simpl. f_equal.
        unfold shift_inv_var. rewrite plus_minus_eq.
        assert (Inb eq_nat_dec x (vars l) = true).
        apply Inb_intro. apply H. hyp.
        rewrite H1. case (le_lt_dec p (x+p)); intro. refl. lia.
      Qed.

    End inverse.

  End shift.

(***********************************************************************)
(** declaration of implicit arguments *)

  Arguments in_vars_shift_min [p x t] _.
  Arguments in_vars_shift_max [p x t] _.
  Arguments sub_shift_incl _ [l] _ [r] _.

(***********************************************************************)
(** red included in shifted red *)

  Section red_incl_shift_red.

    Variables (R R' : rules) (hyp0 : rules_preserve_vars R)
              (hyp : forall a, In a R -> exists p, In (shift_rule p a) R').

    Arguments hyp [a] _.

    Lemma red_incl_shift_red : red R << red R'.

    Proof.
      unfold inclusion. intros. redtac. ded (hyp lr). destruct H as [p].
      rewrite (sub_shift p l) in xl. subst x.
      assert (incl (vars r) (vars l)). apply hyp0. hyp.
      rewrite (sub_shift_incl p s H0) in yr. subst y.
      apply red_rule. hyp.
    Qed.

  End red_incl_shift_red.

(***********************************************************************)
(** shifted red included in red *)

  Section shift_red_incl_red.

    Variables (R R' : rules)
      (hyp : forall a', In a' R' -> exists p a, In a R /\ a' = shift_rule p a).

    Arguments hyp [a'] _.

    Lemma shift_red_incl_red : red R' << red R.

    Proof.
      unfold inclusion. intros. redtac. rename l into l'. rename r into r'.
      subst x. subst y. ded (hyp lr). do 3 destruct H. destruct x0 as [l r].
      simpl in H0. inversion H0. subst l'. subst r'. unfold shift.
      rewrite !sub_sub. apply red_rule. hyp.
    Qed.

  End shift_red_incl_red.

(***********************************************************************)
(** terms with disjoint vars *)

  Definition disjoint_vars t u :=
    forall x, In x (vars t) -> In x (vars u) -> t = u.

  Lemma disjoint_vars_refl t : disjoint_vars t t.

  Proof. unfold disjoint_vars. auto. Qed.

  Lemma disjoint_vars_com t u : disjoint_vars t u -> disjoint_vars u t.

  Proof. unfold disjoint_vars. intros. apply sym_eq. apply (H x); hyp. Qed.

  Definition pw_disjoint_vars l :=
    forall t u, In t l -> In u l -> disjoint_vars t u.

  Lemma pw_disjoint_vars_cons : forall t l, pw_disjoint_vars l ->
    (forall u, In u l -> disjoint_vars t u) -> pw_disjoint_vars (t :: l).

  Proof.
    intros. unfold pw_disjoint_vars. simpl. intros. destruct H1; destruct H2.
    subst t0. subst u. apply disjoint_vars_refl.
    subst t0. auto.
    subst u. apply disjoint_vars_com. apply H0. exact H1.
    apply H; hyp.
  Qed.

(***********************************************************************)
(** shift terms *)

  Fixpoint shift_terms (p : nat) (l : list term) : list term :=
    match l with
    | nil => nil
    | cons t l' => shift p t :: shift_terms (maxvar t + p + 1) l'
    end.

  Lemma in_vars_shift_terms : forall t l p, In t (shift_terms p l) ->
    exists u, exists q, In u l /\ t = shift q u /\ p <= q.

  Proof.
    induction l; simpl; intros. contr. destruct H.
    exists a. exists p. auto.
    ded (IHl _ H). do 3 destruct H0. destruct H1. subst t. exists x. exists x0.
    intuition auto with *.
  Qed.

  Arguments in_vars_shift_terms [t l p] _.

  Lemma in_vars_shift_terms_min : forall p t l x,
      In t (shift_terms p l) -> In x (vars t) -> p <= x.

  Proof.
    intros. ded (in_vars_shift_terms H). do 3 destruct H1. destruct H2. subst t.
    ded (in_vars_shift_min H0). lia.
  Qed.

  Arguments in_vars_shift_terms_min [p t l x] _ _.

  Lemma shift_terms_correct : forall l p, pw_disjoint_vars (shift_terms p l).

  Proof.
    induction l. unfold pw_disjoint_vars. intros. contr.
    intro. simpl. apply pw_disjoint_vars_cons. apply IHl.
    unfold disjoint_vars. intros. ded (in_vars_shift_max H0).
    ded (in_vars_shift_terms_min H H1). absurd (x <= maxvar a + p); lia.
  Qed.

(***********************************************************************)
(** shift rules *)

  Fixpoint shift_rules (p : nat) (R : rules) : rules :=
    match R with
    | nil => nil
    | cons a R' => shift_rule p a :: shift_rules (maxvar(lhs a)+p+1) R'
    end.

  Lemma shift_rules_lhs : forall R p,
      map lhs (shift_rules p R) = shift_terms p (map lhs R).

  Proof.
    induction R; simpl; intros. refl. destruct a. simpl. apply tail_eq.
    apply IHR.
  Qed.

End S.

Arguments in_vars_shift_min [Sig p x t] _.
