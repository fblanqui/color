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

From CoLoR Require Import VRPO_Type VTerm Preorder ListUtil RelUtil
  LogicUtil AccUtil.
From Stdlib Require Import Peano_dec.
From CoLoR Require ListExtras VSubstitution VContext.

Set Implicit Arguments.

Module RPO_Results (Export RPO : RPO_Model).

  Lemma var_are_min : forall x t, lt t (Var x) -> False.

  Proof. intros x t H. lt_inversion H; try inversion t_is. Qed.

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
    gen (IHss H'); clear IHss; intro IHss.
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
    split; [hyp | apply (HInd2 t' t'_in_ts Ht' x x_in_t)].
  Qed.

  Lemma lt_eq_f : forall t s, lt s t -> forall f ts, t = Fun f ts ->
    forall g, g =F= f -> lt s (Fun g ts).

  Proof.
    assert (leF_po : preorder Sig leF).
    apply leF_preorder.
    assert (eqF_trans : transitive eqF).
    elim (eqA_equivalence Sig leF); trivial.
    intros t; induction t as [ | f ts IHt] using term_ind_forall2.
    intros s Hs; elim (var_are_min  Hs).
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
    intros s f g ts f_eq H. eapply lt_eq_f; trivial. eexact H. trivial.
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
    subst s; elim (var_are_min H2).
    apply in_var; trivial.
    apply (@var_inclusion (Fun f ts) s); try right; subst; trivial.
    exists t'; split; trivial.
    elim Ht'; clear Ht'; intro Ht';
      [subst; constructor | apply var_in; trivial].
    apply var_are_min.
              (* case u = (h us) *)
    split.
    intro t; induction t as [x | g ts HInd2] using term_ind_forall2.
              (* case t variable : u < t imposible *)
    intros t H1; elim (var_are_min H1).
		(* case t = (g ts) *)
    intro s; induction s as [x | f ss HInd3] using term_ind_forall2.
              (* case s variable : t < s imposible *)
    intros H1 H2; elim (var_are_min H2).
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
    hyp.
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
    hyp.
              (* case t < s via subterm : *)
    gen (HInd3 t' t'_in_ts H1); intro HInd3'.
    apply (lt_subterm  f1 ts (Fun f0 ss0)).
    exists t'.
    split; trivial.
    right.
    elim Ht'; clear Ht'; intro Ht'.
                      (* case s = g ts : *)
    subst t'; hyp.
                      (* case g ts < s : *)
    apply HInd3'; hyp.
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
    gen (HInd3 t' t'_in_ts H1); intro HInd3'.
    apply (lt_subterm f1 ts (Fun f0 ss0)).
    exists t'.
    split; trivial.
    right.
    elim Ht'; clear Ht'; intro Ht'.
                      (* case s = g ts : *)
    subst t'; hyp.
                      (* case g ts < s : *)
    apply HInd3'; hyp.
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
    subst t'0; right; hyp.
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
    elim (in_exists_element_at s_in_ss); intros p' Hp'.
    elim (eq_nat_dec p p'); intro case_p_p'.
	(* p = p' : *)
    subst p'; rewrite H0 in Hp'.
    inversion Hp'; subst.
    apply lt_subterm.
    exists a'; split; trivial.
    apply exists_element_at_in.
    exists p; apply element_at_replaced.
    elim (@element_at_exists _ ss p); intros H1 H2.
    apply H2; exists s; trivial.
    right; hyp.
	(* p <> p' : *)
    apply lt_subterm.
    exists s; split.
    apply exists_element_at_in.
    exists p'; rewrite <- (@element_at_not_replaced _ ss p' p); trivial.
    intro; elim case_p_p'; subst; trivial.
    left; trivial.
    apply mono_axiom; hyp.
  Qed.

(***********************************************************************)
(* RPO is a reduction ordering *)

  Lemma lt_trans : transitive lt.

  Proof. intros s t u st tu. destruct (SPO_lt s). apply H with t; hyp. Qed.

  Lemma lt_irrefl : irreflexive lt.

  Proof. intros s. destruct (SPO_lt s). trivial. Qed.

  Lemma acc_eq_f : forall f g ss,
    f =F= g -> Acc lt (Fun f ss) -> Acc lt (Fun g ss).

  Proof.
    intros f g ss f_eq Hacc.
    inversion Hacc.
    constructor.
    intros t Ht.
    apply H.
    eapply (lt_eq_f Ht); trivial.
  Qed.
    
  Lemma Acc_lt_var : forall x, Acc lt (Var x).

  Proof.
    intro x; constructor; intros t lt_t_var_x. elim (var_are_min lt_t_var_x).
  Qed.

  Import ListExtras.

  Lemma eqF_sym : forall f g, f =F= g -> g =F= f.

  Proof.
    intros. destruct (eqA_equivalence Sig leF). apply leF_preorder.
    unfold eqF; intuition.
  Defined.

  Import VSubstitution VContext RPO.P.

  Section subst_closed.

  Variable status_homomorphic : forall F ss ts f,
    (forall s t, In s ss -> In t ts -> lt s t -> lt (F s) (F t)) ->
    tau f lt ss ts -> tau f lt (map F ss) (map F ts).

  Lemma lt_subst_closed : substitution_closed lt.

  Proof.
    intros p q. gen p. clear p.
    pattern q. apply well_founded_ind with term (@subterm Sig).
    apply subterm_wf. clear q.
    intros q IH p. gen IH. clear IH.
    pattern p. apply well_founded_ind with term (@subterm Sig).
    apply subterm_wf. clear p. intros p IH IH'.
    destruct q.
     (* variable *)
    intros. exfalso. eapply var_are_min. eexact H.
     (* fun. *)
     (* lt_roots *)
    intros. lt_inversion H.
    subst p. simpl.
    apply lt_roots. replace f with g. hyp. congruence.
    intros. rewrite <- sub_fun.
    destruct (proj1 (in_map_iff (sub s) ss t)) as [t' [t't t'ss]]. hyp.
    subst t. apply IH. apply subterm_immediate. hyp. hyp.
    rewrite t_is. apply Hsub. hyp.
     (* lt_status *)
    subst p. do 2 rewrite sub_fun.
    apply lt_status. apply eqF_sym. replace f with g. hyp. congruence.
    intros. rewrite <- sub_fun.
    destruct (proj1 (in_map_iff (sub s) ss t)) as [t' [t't t'ss]]. hyp.
    subst t. apply IH. apply subterm_immediate. hyp. hyp.
    rewrite t_is. apply Hsub. hyp.
    replace f with g; [rewrite <- (status_eq f0 g eqFfg) | congruence].
    apply status_homomorphic. intros.
    apply IH'. apply subterm_immediate. hyp. hyp. congruence.    
     (* lt_subterm *)
    rewrite sub_fun. apply lt_subterm.
    exists (sub s t'). split.
    apply (proj2 (in_map_iff (sub s) l (sub s t'))).
    exists t'. split. refl. replace l with ts. hyp. congruence.
    destruct Ht'.
    left. congruence.
    right. apply IH'. apply subterm_immediate. replace l with ts.
    hyp. congruence. hyp.
  Qed.
   
  End subst_closed. 

  Lemma wf_lt : well_founded lt.

  Proof.
    intro s; induction s as [ | f ss HInd1] using term_ind_forall2.
	      (* case s variable : *)
    apply Acc_lt_var.
	      (* case s = f ss : *)
    revert ss HInd1.
    induction (wf_ltF f) as [f acc_f HInd2].
    intros ss Hss; cut (Restricted_acc (Accs lt) (tau f lt) ss).
    intro Acc_ss; gen Hss; clear Hss.
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
    assert (HAccs : Accs lt ts).
    intros ti ti_in_ts.
    apply HInd4; trivial.
    apply Hsub; trivial.
    assert (H' : Acc lt (Fun f ts)).
    apply HInd3; trivial.
    rewrite <- (status_eq g f eqFfg); trivial.
    apply acc_eq_f with f; trivial; elim eqFfg; split; trivial.
	      (* case t < s via subterm : *)
    subst f0 ts0.
    gen (Hss t' t'_in_ts); intro acc_t'.
    elim Ht'; [intro; subst t'; trivial | gen (Fun g ts)].
    inversion acc_t'; hyp.
    apply (status_lifting f).
    intros s s_in_ss; apply Hss; trivial.
  Qed.

  Lemma eqF_dec : forall f g, {f =F= g} + {~f =F= g}.

  Proof.
    intros. unfold eqF, eqA.
    destruct (leF_dec f g). destruct (leF_dec g f).
    auto. right. tauto. right. tauto.
  Defined.

  Lemma ltF_dec : forall f g, {f <F g} + {~f <F g}.

  Proof.
    intros. unfold ltF, ltA, eqA.
    destruct (leF_dec f g). destruct (leF_dec g f).
    right. tauto. left. tauto. right. tauto.
  Defined.

  Definition term_eq (tu : term * term) :=
    let (t, u) := tu in if term_eq_dec t u then true else false.

  Lemma term_eq_correct : forall t u, term_eq (t, u) = true -> t = u.

  Proof.
    intros. unfold term_eq in H. destruct (term_eq_dec t u). hyp. discr.
  Qed.

  Notation term_eq_dec := (@term_eq_dec Sig).

  Definition ge p q := lt q p \/ p = q.

  Lemma rpo_lt_subterm_dec : forall p v
    (IH : forall t, Inb term_eq_dec t v = true
      -> forall  p, {lt p t} + {~lt p t}),
    { a : term | In a v /\ ge a p } + { ~exists a : term, In a v /\ ge a p }.

  Proof.
    intros. destruct (many_one_dec ge v p).
    intros. destruct (IH x (Inb_intro term_eq_dec x v H) p).
    left. left. hyp.
    destruct (term_eq_dec x p).
    left. right. hyp.
    right. intro abs. destruct abs; contr.
    left. exact s.
    right. intro abs. destruct abs as [a [av ap]]. 
    apply (n a); hyp.
  Defined.

  Lemma rpo_lt_dec : rel_dec lt.

  Proof.
     (*   A bit of juggling to make an induction on pair of terms 
      * ordered lexicographically (by nested induction). 
      *   Still seems to be easier than to instantiate one of 
      * lexicographic order definitions.
      *)
    intros p q. gen p. clear p. pattern q. 
    apply term_rect_forall with Sig term_eq_dec.
     (* Compare: lt p (Var x) *)
    right. intro F. apply var_are_min with x p. hyp.
    clear q. intros q v IH p.
    gen IH. clear IH. pattern p.
    apply term_rect_forall with Sig term_eq_dec; clear p.
     (* Compare: lt (Var x) (Fun q v) *)
    intros x IH. destruct (rpo_lt_subterm_dec (Var x) v). hyp.
    left. apply lt_subterm. destruct s as [a [av ax]].
    exists a. unfold ge in ax. split_all.
    right. intro H. lt_inversion H; try discr.
    apply n. exists t'. replace v with ts. unfold ge. split_all. congruence.
     (* Compare: lt (Fun f vf) (Fun g v) *)
    intros f vf IH IH'.
    destruct (rpo_lt_subterm_dec (Fun f vf) v). hyp.
    left. apply lt_subterm. destruct s as [a [av ax]].
    exists a. unfold ge in ax. split_all.
    assert (all_lt_dec : 
      { forall t, In t vf -> lt t (Fun q v) } + 
      { exists t, In t vf /\ ~lt t (Fun q v) }).
    destruct (list_dec_all (fun vs => lt vs (Fun q v)) vf);
      try solve [split_all].
    intros. apply IH. apply Inb_intro. hyp. hyp. 
     (* RPO clause: lt_roots *)
    assert (lt_roots_dec : {lt (Fun f vf) (Fun q v)} + 
      {~(f <F q) \/ exists t, In t vf /\ ~lt t (Fun q v)}).
    destruct (ltF_dec f q); try solve [split_all].
    destruct all_lt_dec; split_all.
    left. apply lt_roots; hyp.
    destruct lt_roots_dec. split_all.
     (* RPO clause: lt_status *)
    assert (lt_status_dec : {lt (Fun f vf) (Fun q v)} + 
      {~f =F= q \/ ~tau q lt vf v \/ exists t, In t vf /\ ~lt t (Fun q v)}).
    destruct (eqF_dec f q); try solve [split_all].
    destruct (tau_dec q lt vf v); try solve [split_all].
    intros. apply (IH' s). apply Inb_intro. hyp. 
    destruct all_lt_dec; try solve [split_all].
    left. apply lt_status; try solve [split_all].
    apply eqF_sym. hyp.
    destruct lt_status_dec. split_all.
     (* proof that order does not hold *)
    right. intro ord. lt_inversion ord.
    destruct o as [f_q | [t [t_vf t_qv]]].
    apply f_q. congruence.
    apply t_qv. replace q with g; replace v with ts; try solve [congruence].
    apply Hsub. congruence. 
    destruct o0 as [f_q | [tau_vfv | [t [t_vf t_qv]]]].
    apply f_q. congruence.
    apply tau_vfv. rewrite (status_eq q f0). congruence.
    apply eqF_sym. congruence.
    apply t_qv. replace q with g; replace v with ts; try solve [congruence].
    apply Hsub. congruence.
    apply n. exists t'. split. congruence.
    unfold ge. split_all.
  Defined.

End RPO_Results.
