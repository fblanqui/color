(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Proofs of a relation verifying Hypotheses in RPO_Type is 
a well-founded monotonic strict order
*)

(* $Id: VRPO_Results.v,v 1.2 2007-01-19 17:22:39 blanqui Exp $ *)

Require Export VRPO_Type.

Module RPO_Symb_Beh_Facts (RPO : RPO_Axioms_Type).

  Export RPO.
  
  Lemma var_are_min : forall x t, lt t (Var x) -> False.

  Proof.
    intros x t H. lt_inversion H; try inversion t_is.
  Qed.

  Inductive in_term_vars : variable -> term -> Prop :=
    | is_var : forall x, in_term_vars x (Var x)
    | is_in_list : forall x f ss,
      ex (fun s => In s ss /\ in_term_vars x s) -> in_term_vars x (Fun f ss).

  Lemma var_in : forall x t, lt (Var x) t -> in_term_vars x t.

  Proof. 
    intros x t; induction t as [y| f ts IHt] using term_ind_forall2; intro H.
    lt_inversion H; try inversion t_is.
    lt_inversion H; try inversion t_is; try inversion s_is.
    constructor; exists t'; split; trivial.
    subst; elim Ht'; clear Ht'; intro Ht'.
    subst; constructor.
    apply IHt; trivial.
  Qed.

  Lemma eq_elem_to_eq_list_dec : forall ss : terms,
    (forall s, In s ss -> forall t, s = t \/ s <> t) ->
    forall ts, ss = ts \/ ss <> ts.

  Proof.
    intro ss; induction ss as [ | s ss IHss]; intros Hss ts.
    destruct ts; [left; trivial | right; intro H; inversion H].
    destruct ts as [ | t ts]; [right; intro H; inversion H | idtac].
    assert (H : In s (s :: ss)).
    left; trivial.
    elim (Hss s H t); intro case_s_t.
    subst t.
    assert (H' : forall s, In s ss -> forall t, s = t \/ s <> t).
    intros s' s'_in_ss; apply Hss; try right; trivial.
    generalize (IHss H'); clear IHss; intro IHss.
    elim (IHss ts); intro case_ts.
    subst ss; left; trivial.
    right; injection; trivial.
    right; injection; trivial.
  Qed.

  Lemma eq_term_dec : forall s t : term, s = t \/ s <> t.

  Proof.
    intro s; induction s as [x | f ss IHs] using term_ind_forall2.
    intro t; destruct t as [y | g ts].
    elim (eq_nat_dec x y); intro; [left; subst | right; injection]; trivial.
    right; intro H; inversion H.
    intro t; destruct t as [y | g ts].
    right; intro H; inversion H.
    elim (eq_symb_dec f g); intro case_f.
    subst g.
    elim (eq_elem_to_eq_list_dec ss IHs ts); intro case_ss_ts.
    subst; left; trivial.
    right; injection; trivial.
    right; injection; trivial.
  Qed.

  Lemma in_var : forall x t, t <> Var x -> in_term_vars x t -> lt (Var x) t.

  Proof.
    intros x t; induction t as [y| f ts IHt] using term_ind_forall2;
      intros Hneq H; inversion H.
    elim Hneq; subst; trivial.
    subst.
    elim H2; clear H2; intros s Hs; elim Hs; clear Hs; intros s_in_ss Hs.
    apply lt_subterm; exists s; split; trivial.
    elim (eq_term_dec s (Var x)); intro case_s.
    left; trivial.
    right; apply (IHt s s_in_ss case_s Hs).
  Qed.

  Lemma immediate_subterm_property : forall s f ss, In s ss -> lt s (Fun f ss).

  Proof.
    intros s f ss Hin.
    apply lt_subterm.
    exists s.
    split; try left; trivial.
  Qed.

  Lemma var_inclusion : forall t s, lt t s -> forall x,
    in_term_vars x t -> in_term_vars x s.

  Proof.
    intro t; induction t as [x | g ts HInd1] using term_ind_forall2.
	(* case t  = var x *)
    intros s Hts x0 Hx0.
	(* Hx0 says x0 is in vars x, so x = x0 *) 
    inversion Hx0.
    subst.
    lt_inversion Hts; subst; try inversion s_is.
    apply var_in; trivial.
	(* case t = g ts *) 
    induction s as [x | f ss HInd2] using term_ind_forall2.
	(* case s = Var x : t < s imposible *)
    intro Hst; lt_inversion Hst; try inversion s_is; try inversion t_is.
	(* case s = f ss *)
    intros Hts x x_in_t.
    lt_inversion Hts; try inversion s_is; try inversion t_is; subst. 
	(*  root : *)
    inversion x_in_t; subst.
    elim H1; clear H1; intros tx H1.
    elim H1; clear H1; intros tx_in_ss Htx.
    apply (HInd1 tx tx_in_ss (Fun g0 ts0) (Hsub tx tx_in_ss) x Htx). 
	(* status : *)
    inversion x_in_t; subst.
    elim H1; clear H1; intros tx H1.
    elim H1; clear H1; intros tx_in_ss Htx.
    apply (HInd1 tx tx_in_ss (Fun g0 ts0)); trivial.
    apply Hsub; trivial.
	(* subterm : *)
    elim Ht'; clear Ht'; intro Ht'.
          (* case t' = t : *)
    constructor.
    exists t'; split; trivial.
    subst; trivial.
          (* case t < t' *)
    constructor.
    exists t'.
    split; [assumption | apply (HInd2 t' t'_in_ts Ht' x x_in_t)].
  Qed.

  Lemma lt_eq_f : forall t s, lt s t -> forall f ts, t = Fun f ts ->
    forall g, g =F= f -> lt s (Fun g ts).

  Proof.
    assert (leF_po : preorder Sig leF).
    apply leF_preorder.
    assert (eqF_trans : transitive eqF).
    elim (eqA_equivalence Sig leF); trivial.
    intros t; induction t as [ | f ts IHt] using term_ind_forall2.
    intros s Hs; elim (var_are_min x s Hs).
    intro s; induction s as [ | g ss IHs] using term_ind_forall2. 
    intros Hs f' ts' Heq; inversion Heq; subst.
    lt_inversion Hs; try inversion s_is; try inversion t_is; subst.
    intros g Hg; apply lt_subterm; exists t'.
    split; trivial.
    elim Ht'; clear Ht'; intro Ht'; [subst ; left| right]; trivial.
    intros Hs f' ts' Heq; inversion Heq; subst.
    intros g' g'_eq.
    lt_inversion Hs; try inversion s_is; try inversion t_is; subst.
              (* case root : *)
    apply lt_roots.
    apply (ltA_eqA_compat_r Sig leF) with g0; trivial.
    elim g'_eq; split; trivial.
    intros t t_in_ss.
    apply (IHs t t_in_ss (Hsub t t_in_ss) g0 ts); trivial.
              (* case status : *)
    apply lt_status.
    apply eqF_trans with g0; trivial.
    elim eqFfg; split; trivial.
    intros t t_in_ss.
    apply (IHs t t_in_ss (Hsub t t_in_ss) g0 ts); trivial.
    assert (Seq : tau g' = tau f).
    apply status_eq.
    apply eqF_trans with g0; trivial.
    elim eqFfg; split; trivial.
    rewrite Seq; trivial.
            (* case subterm : *)
    apply lt_subterm; exists t'; split; trivial.
    elim Ht'; [left; subst | right]; trivial.
  Qed.

  Lemma lt_eq_f' : forall s f g ts,
    g =F= f -> lt s (Fun f ts) -> lt s (Fun g ts).

  Proof.
    intros s f g ts f_eq H; apply (lt_eq_f (Fun f ts) s) with f; trivial.
  Qed.

End RPO_Symb_Beh_Facts.

(***********************************************************************)

Module RPO_MSO_Facts (RPO : RPO_MSO_Type).

  Export RPO.

  Module RPO_SBF := RPO_Symb_Beh_Facts RPO.Base.
  Export RPO_SBF.

  Lemma SPO_lt : forall u,
    (forall t s, lt u t -> lt t s -> lt u s) /\ (lt u u -> False).

  Proof.
    assert (leF_po : preorder Sig leF).
    apply leF_preorder.
    assert (ltF_trans : transitive ltF).
    apply (ltA_trans Sig leF); trivial.
    assert (eqF_trans : transitive eqF).
    elim (eqA_equivalence Sig leF); trivial.
    assert (ltF_irrefl : forall f, f <F f -> False).
    intros f Hf; apply (ltA_antisym Sig leF f f); trivial.
    intro u; induction u as [x | h us HInd1] using term_ind_forall2.
              (* case u variable : *)
    split.
    intros t s H1 H2.
                      (* case u < t : *)
    lt_inversion H1; try inversion s_is; try inversion t_is.
                      (* x < s : *)
    elim (eq_term_dec s (Var x)); intro case_s.
    subst s; elim (var_are_min x t H2).
    apply in_var; trivial.
    apply (var_inclusion (Fun f ts) s); try right; subst; trivial.
    exists t'; split; trivial.
    elim Ht'; clear Ht'; intro Ht';
      [subst; constructor | apply var_in; trivial].
    apply var_are_min.
              (* case u = (h us) *)
    split.
    intro t; induction t as [x | g ts HInd2] using term_ind_forall2.
              (* case t variable : u < t imposible *)
    intros t H1; elim (var_are_min x _ H1).
		(* case t = (g ts) *)
    intro s; induction s as [x | f ss HInd3] using term_ind_forall2.
              (* case s variable : t < s imposible *)
    intros H1 H2; elim (var_are_min x _ H2).
              (* case s = (f ss) *)
    intros H1 H2.
    lt_inversion H1; try inversion s_is; try inversion t_is; subst.
              (* case u < t via roots : *)
    lt_inversion H2; try inversion s_is0; try inversion t_is0; subst.
              (* case t < s via roots : *)
    apply lt_roots.
                      (* f < h : *)
    apply ltF_trans with f1; trivial.
                      (* ui < s : *)
    intros u u_in_us.
    elim (HInd1 u u_in_us); clear HInd1; intros HInd1 HInd1'.
    apply (HInd1 (Fun f1 ss1) (Fun g ts)).
    apply (Hsub u u_in_us).
    assumption.
              (* case t < s via status : *)
    apply lt_roots.
                      (* f < h : *)
    apply (ltA_eqA_compat_r Sig leF) with f1; trivial;
      elim geq; split; trivial.
                      (* u < s  : *)
    intros u u_in_us.
    elim (HInd1 u u_in_us); clear HInd1; intros HInd1 HInd1'.
    apply (HInd1 (Fun f1 ss1)).
    apply (Hsub u u_in_us).
    assumption.
              (* case t < s via subterm : *)
    generalize (HInd3 t' t'_in_ts H1); intro HInd3'.
    apply (lt_subterm  f1 ts (Fun f0 ss0)).
    exists t'.
    split; trivial.
    right.
    elim Ht'; clear Ht'; intro Ht'.
                      (* case s = g ts : *)
    subst t'; assumption.
                      (* case g ts < s : *)
    apply HInd3'; assumption.
              (* case u < t via status : *)
    lt_inversion H2; try inversion s_is0; try inversion t_is0; subst.
              (* case t < s via roots : *)
    apply lt_roots.
                      (* g < h : *)
    apply (ltA_eqA_compat_l Sig leF) with f1; trivial.
    elim eqFfg; split; trivial.
                      (* u < s : *)
    intros u u_in_us.
    elim (HInd1 u u_in_us); clear HInd1; intros HInd1 HInd1'.
    apply (HInd1 (Fun f1 ss1)); trivial.
    apply (HInd1 (Fun f0 ss0)); trivial.
    apply lt_subterm; exists u; split; try left; trivial.
              (* case t < s via rpo2lex : *)
    apply lt_status; trivial.
    apply eqF_trans with f1; trivial.
    elim eqFfg0; split; trivial.
    elim eqFfg; split; trivial.
    intros u u_in_us; elim (HInd1 u u_in_us); clear HInd1; intros HInd1 HInd1'.
    apply (HInd1 (Fun f1 ss1)); trivial.
    apply Hsub; trivial.
		(* status f lt us ss : *)
    assert (Hs1 : tau f1 = tau g).
    apply status_eq; trivial.
    assert (Hs2 : tau f0 = tau f1).
    apply status_eq; trivial.
    rewrite <- Hs1.
    elim (SPO_to_status_SPO f1 lt ss0 HInd1); intros trans_to_status_trans H'. 
    apply trans_to_status_trans with ss1; trivial.
    rewrite <- Hs2; trivial.
              (* case t < s via subterm : *)
    generalize (HInd3 t' t'_in_ts H1); intro HInd3'.
    apply (lt_subterm f1 ts (Fun f0 ss0)).
    exists t'.
    split; trivial.
    right.
    elim Ht'; clear Ht'; intro Ht'.
                      (* case s = g ts : *)
    subst t'; assumption.
                      (* case g ts < s : *)
    apply HInd3'; assumption.
              (* case u < t via subterm : *)
    lt_inversion H2; try inversion s_is; try inversion t_is0; subst.
              (* case t < s via root : *)
    elim Ht'; clear Ht'; intro Ht'.
    rewrite Ht'; apply (Hsub t' t'_in_ts).
    apply (HInd2 t' t'_in_ts (Fun g ts) Ht').
    apply (Hsub t' t'_in_ts).
              (* case t < s via status : *)
    elim Ht'; clear Ht'; intro Ht'.
    rewrite Ht'.
    apply Hsub; trivial.
    apply (HInd2 t' t'_in_ts (Fun g ts)); trivial.
    apply Hsub; trivial.
              (* case t < s via status : *)
    apply lt_subterm.
    exists t'0.
    split; trivial.
    elim Ht'0; clear Ht'0; intro Ht'0.
    subst t'0; right; assumption.
    right; apply (HInd3 t'0 t'_in_ts0); trivial.
    intro H.
    lt_inversion H; try inversion t_is; subst; try inversion s_is; subst.
    apply (ltF_irrefl f); trivial.
    elim (SPO_to_status_SPO f lt ss HInd1);
      intros trans_to_status_trans irrefl_to_status_irrefl. 
    apply (irrefl_to_status_irrefl); trivial.
    elim (HInd1 t' t'_in_ts); intros HInd1' HInd1''.
    elim Ht'; clear Ht'; intro Ht'.
    apply HInd1''; subst; trivial.
    apply HInd1''.
    apply HInd1' with (Fun f ts); trivial.
    apply immediate_subterm_property; trivial.
  Qed.

(***********************************************************************)
(* monotonicity *)
  
  Lemma monotonic_lt : forall f ss ts,
    one_less lt ss ts -> lt (Fun f ss) (Fun f ts).

  Proof.
    assert (leF_po : preorder Sig leF).
    apply leF_preorder.
    intros f ss ts Hol.
    apply lt_status.
    elim (leF_po); intros leF_refl leF_trans.
    split; apply leF_refl.
    intros s s_in_ss.
    inversion Hol; subst.
    elim (in_element_at ss s s_in_ss); intros p' Hp'.
    elim (eq_nat_dec p p'); intro case_p_p'.
	(* p = p' : *)
    subst p'; rewrite H0 in Hp'.
    inversion Hp'; subst.
    apply lt_subterm.
    exists a'; split; trivial.
    apply (element_at_in).
    exists p; apply element_at_replaced.
    elim (element_at_exists ss p); intros H1 H2.
    apply H2; exists s; trivial.
    right; assumption.
	(* p <> p' : *)
    apply lt_subterm.
    exists s; split.
    apply element_at_in.
    exists p'; rewrite <- (@element_at_not_replaced _ ss p' p); trivial.
    intro; elim case_p_p'; subst; trivial.
    left; trivial.
    apply mono_axiom; assumption.
  Qed.

End RPO_MSO_Facts.

(***********************************************************************)
(* well-foundedness *)

Module RPO_Wf_Facts (RPO : RPO_Wf_Type).

  Export RPO.

  Module RPO_SBF := RPO_Symb_Beh_Facts RPO.Base.
  Export RPO_SBF.

  Lemma acc_eq_f : forall f g ss,
    f =F= g -> Acc lt (Fun f ss) -> Acc lt (Fun g ss).

  Proof.
    intros f g ss f_eq Hacc.
    inversion Hacc.
    constructor.
    intros t Ht.
    apply H.
    apply (lt_eq_f (Fun g ss) t Ht g ss); trivial.
  Qed.
    
  Lemma Acc_lt_var : forall x, Acc lt (Var x).

  Proof.
    intro x; constructor; intros t lt_t_var_x.
    elim (var_are_min x t); assumption.
  Qed.
    
  Theorem wf_lt : well_founded lt.

  Proof.
    intro s; induction s as [ | f ss HInd1] using term_ind_forall2.
	      (* case s variable : *)
    apply Acc_lt_var.
	      (* case s = f ss : *)
    generalize ss HInd1; clear HInd1 ss.
    induction (wf_ltF f) as [f acc_f HInd2].
    intros ss Hss; cut (Restricted_acc (accs lt) (tau f lt) ss).
    intro Acc_ss; generalize Hss; clear Hss.
    induction Acc_ss as [ss Acc_ss HInd3].
    intro Hss; constructor; intro t;
      induction t as [ | g ts HInd4] using term_ind_forall2; intro H.
	      (* case t variable : *)
    apply Acc_lt_var.
	      (* case t = g ts : *)
    lt_inversion H; try inversion s_is; try inversion t_is;
      try subst f0 ss0; try subst g0 ts0.
	      (* case t < s via roots : *)
    apply (HInd2 g ltFfg ts).
		      (* all terms in ts are accessibles : *)
    intros t t_in_ts.
    apply (HInd4 t t_in_ts).
    apply (Hsub t t_in_ts).
	      (* case t < s via status : *)
    assert (Haccs : accs lt ts).
    intros ti ti_in_ts.
    apply HInd4; trivial.
    apply Hsub; trivial.
    assert (H' : Acc lt (Fun f ts)).
    apply HInd3; trivial.
    rewrite <- (status_eq g f eqFfg); trivial.
    apply acc_eq_f with f; trivial; elim eqFfg; split; trivial.
	      (* case t < s via subterm : *)
    subst f0 ts0.
    generalize (Hss t' t'_in_ts); intro acc_t'.
    elim Ht'; [intro; subst t'; trivial | generalize (Fun g ts)].
    inversion acc_t'; assumption.
    apply (status_lifting f).
    intros s s_in_ss; apply Hss; trivial.
  Qed.

End RPO_Wf_Facts.
