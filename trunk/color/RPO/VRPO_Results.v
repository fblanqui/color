(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09
- Adam Koprowski, 2007-06-03, added section proving that RPO is a 
   reduction ordering + a number of smaller things for certification
   of examples.

Proofs of a relation verifying Hypotheses in RPO_Type is 
a well-founded monotonic strict order
*)

(* $Id: VRPO_Results.v,v 1.11 2007-06-04 00:22:19 koper Exp $ *)

Require Export VRPO_Type.

Module RPO_Results (RPO : RPO_Model).

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

  Lemma in_var : forall x t, t <> Var x -> in_term_vars x t -> lt (Var x) t.

  Proof.
    intros x t; induction t as [y| f ts IHt] using term_ind_forall2;
      intros Hneq H; inversion H.
    elim Hneq; subst; trivial.
    subst.
    elim H2; clear H2; intros s Hs; elim Hs; clear Hs; intros s_in_ss Hs.
    apply lt_subterm; exists s; split; trivial.
    elim (term_eq_dec s (Var x)); intro case_s.
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

(***********************************************************************)

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
    elim (term_eq_dec s (Var x)); intro case_s.
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

(***********************************************************************)
(* RPO is a reduction ordering *)

  Lemma lt_trans : transitive lt.

  Proof.
    intros s t u st tu. destruct (SPO_lt s). apply H with t; assumption.
  Qed.

  Lemma lt_irrefl : irreflexive lt.

  Proof.
    intros s. destruct (SPO_lt s). trivial.
  Qed.

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

  Require Import ListExtras.

  Lemma eqF_sym : forall f g, f =F= g -> g =F= f.

  Proof.
    intros. destruct (eqA_equivalence Sig leF). apply leF_preorder.
    unfold eqF; intuition.
  Qed.

  Require Import VSubstitution.
  Require Import VContext.

  Section subst_closed.

  Variable status_homomorphic : forall F ss ts f,
    (forall s t, In s ss -> In t ts -> lt s t -> lt (F s) (F t)) ->
    tau f lt ss ts -> tau f lt (map F ss) (map F ts).

  Lemma lt_subst_closed : substitution_closed lt.

  Proof.
    intros p q. generalize p. clear p.
    pattern q. apply well_founded_ind with term (@subterm Sig).
    apply subterm_wf. clear q.
    intros q IH p. generalize IH. clear IH.
    pattern p. apply well_founded_ind with term (@subterm Sig).
    apply subterm_wf. clear p. intros p IH IH'.
    destruct q.
     (* variable *)
    intros. elimtype False. eapply var_are_min. eexact H.
     (* fun. *)
     (* lt_roots *)
    intros. lt_inversion H.
    subst p. do 2 rewrite app_fun.
    apply lt_roots. replace f with g. assumption. congruence.
    intros. rewrite <- app_fun.
    destruct (proj1 (in_map_iff (app s) ss t)) as [t' [t't t'ss]]. assumption.
    subst t. apply IH. apply subterm_immediate. assumption. assumption.
    rewrite t_is. apply Hsub. assumption.
     (* lt_status *)
    subst p. do 2 rewrite app_fun.
    apply lt_status. apply eqF_sym. replace f with g. assumption. congruence.
    intros. rewrite <- app_fun.
    destruct (proj1 (in_map_iff (app s) ss t)) as [t' [t't t'ss]]. assumption.
    subst t. apply IH. apply subterm_immediate. assumption. assumption.
    rewrite t_is. apply Hsub. assumption.
    replace f with g; [rewrite <- (status_eq f0 g eqFfg) | congruence].
    apply status_homomorphic. intros.
    apply IH'. apply subterm_immediate. assumption. assumption. congruence.    
     (* lt_subterm *)
    rewrite app_fun. apply lt_subterm.
    exists (app s t'). split.
    apply (proj2 (in_map_iff (app s) l (app s t'))).
    exists t'. split. refl. replace l with ts. assumption. congruence.
    destruct Ht'.
    left. congruence.
    right. apply IH'. apply subterm_immediate. replace l with ts.
    assumption. congruence. assumption.
  Qed.
   
  End subst_closed. 

  Lemma wf_lt : well_founded lt.

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

  Lemma eqF_dec : forall f g, {f =F= g} + {~f =F= g}.

  Proof.
    intros. unfold eqF, eqA.
    destruct (leF_dec f g); intuition.
    destruct (leF_dec g f); intuition.
  Defined.

  Lemma ltF_dec : forall f g, {f <F g} + {~f <F g}.

  Proof.
    intros. unfold ltF, ltA, eqA.
    destruct (leF_dec f g); intuition.
    destruct (leF_dec g f); intuition.    
  Defined.

  Lemma rpo_lt_dec : rel_dec lt.

  Proof.
     (*   A bit of juggling to make an induction on pair of terms 
      * ordered lexicographically (by nested induction). 
      *   Still seems to be easier than to instantiate one of 
      * lexicographic order definitions.
      *)
    intros p q. generalize p. clear p.
    pattern q. apply well_founded_induction with term (@subterm Sig).
    apply subterm_wf. clear q.
    intros q IH p. generalize IH. clear IH.
    pattern p. apply well_founded_induction with term (@subterm Sig).
    apply subterm_wf. clear p. intros p IH IH'.
    destruct q.
     (* Compare: lt p (Var n) *)
    right. intro F. apply var_are_min with n p. assumption.
     (* Compare: lt p (Fun f l) *)
    set (ge := fun x y => lt y x \/ x = y).
    destruct (many_one_dec ge l p).
    intros. destruct (IH' l0 (subterm_immediate f l l0 H) p).
    left. left. assumption.
    destruct (term_eq_dec l0 p).
    left. right. assumption.
    right. intro. destruct H0; auto.
    left. destruct s as [q [lq pa]]. apply lt_subterm. exists q. 
    destruct pa; split; intuition.
    destruct p.
     (* Compare: lt (Var n0) (Fun f l) *)
    right. intro H. lt_inversion H; try discriminate.
    absurd (ge t' (Var n0)).
    apply n. congruence.
    destruct Ht'; [right | left]; intuition.
     (* Compare: lt (Fun f0 l0) (Fun f l) *)
    assert (all_lt_dec : 
      { forall l0a, In l0a l0 -> lt l0a (Fun f l) } + 
      { exists l0a, In l0a l0 /\ ~lt l0a (Fun f l) }).
    destruct (list_dec_all (fun v => lt v (Fun f l)) l0); try solve [intuition].
    intros. destruct (IH l1); intuition.
    apply subterm_immediate. assumption.
     (* RPO clause: lt_roots *)
    assert (lt_roots_dec : {lt (Fun f0 l0) (Fun f l)} + 
      {~(f0 <F f) \/ exists t, In t l0 /\ ~lt t (Fun f l)}).
    destruct (ltF_dec f0 f); try solve [intuition].
    destruct all_lt_dec; intuition.
    left. apply lt_roots; assumption.
    destruct lt_roots_dec. intuition.
     (* RPO clause: lt_status *)
    assert (lt_status_dec : {lt (Fun f0 l0) (Fun f l)} + 
      {~f0 =F= f \/ ~tau f lt l0 l \/ exists t, In t l0 /\ ~lt t (Fun f l)}).
    destruct (eqF_dec f0 f); try solve [intuition].
    destruct (tau_dec f lt l0 l); try solve [intuition].
    intros. apply (IH' s). apply subterm_immediate. assumption.
    destruct all_lt_dec; try solve [intuition].
    left. apply lt_status; try solve [intuition].
    apply eqF_sym. assumption.
    destruct lt_status_dec. intuition.
     (* proof that order does not hold *)
    right. intro ord. lt_inversion ord.
    destruct o as [f0_f | [t [t_l0 t_fl]]].
    apply f0_f. congruence.
    apply t_fl. replace f with g; replace l with ts; try solve [congruence].
    apply Hsub. congruence. 
    destruct o0 as [f0_f | [tau_l0l | [t [t_l0 t_fl]]]].
    apply f0_f. congruence.
    apply tau_l0l. rewrite (status_eq f f1). congruence. 
    apply eqF_sym. congruence.
    apply t_fl. replace f with g; replace l with ts; try solve [congruence].
    apply Hsub. congruence.
    absurd (ge t' (Fun f0 l0)).
    apply n. congruence. destruct Ht'. 
    right. auto.
    left. assumption.
  Defined.

End RPO_Results.
