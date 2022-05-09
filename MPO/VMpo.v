(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2005-09-19

This file provides a definition of the multiset path ordering and proofs
that it preserves various properties
*)

From CoLoR Require Import AccUtil MultisetOrder ListExtras RelExtras
  MultisetCore MultisetList MultisetTheory MultisetListOrder VTerm RelUtil
  LogicUtil.
From Coq Require Import Permutation Arith Setoid.

Module Type VMpo_Struct.
  Parameter Sig : Signature.
  Parameter ltF : relation Sig.
  Parameter wf_ltF : well_founded ltF.
  Parameter ltF_trans : transitive ltF.  
End VMpo_Struct.

Module Make (Import S : VMpo_Struct).

  Notation term := (term Sig).
  Notation terms := (list term).

(***********************************************************************)
(** eqset module of terms *)

  Module Term <: Eqset.

    Definition A := term.

    Definition eqA := eq (A := term).
    Notation "X =A= Y" := (eqA X Y) (at level 70).

    #[global] Instance eqA_Equivalence : Equivalence eqA.

    Proof.
      constructor; unfold Reflexive, Symmetric, Transitive.
      unfold eqA; simpl; trivial.
      unfold eqA; intros; subst; trivial.
      unfold eqA; intros; subst; trivial.
    Qed.

  End Term.

  Module Term_dec <: Eqset_dec.

    Module Export Eq := Term.

    Definition eqA_dec := @term_eq_dec Sig.

  End Term_dec.

(***********************************************************************)
(** multisets on terms *)
  
  Module Export LMO := MultisetListOrder.MultisetListOrder Term_dec.

(***********************************************************************)
(** mpo *)

  Inductive lt_mpo : relation term :=
  | mpo1 : forall f g ss ts, ltF g f -> 
    (forall t, In t ts -> lt_mpo t (Fun f ss)) -> lt_mpo (Fun g ts) (Fun f ss)
  | mpo2 : forall f ss ts,
    mult (transp lt_mpo) ts ss -> lt_mpo (Fun f ts) (Fun f ss)
  | mpo3 : forall t f ss, 
    ex (fun s => In s ss /\ (s = t \/ lt_mpo t s)) -> lt_mpo t (Fun f ss).

  Notation "ss << ts" := (mult (transp term lt_mpo) ss ts) (at level 50).

(* Warning: Ignoring recursive call (since lt_mpo_ind unused, seems ok) *)

  Definition le_mpo := fun t s => t = s \/ lt_mpo t s.

(***********************************************************************)
(** compatibility with setoid equality *)

  Lemma tlt_mpo_eqA_compat : forall x x' y y', 
    eqA x x' -> eqA y y' -> transp lt_mpo x y -> transp lt_mpo x' y'.

  Proof. unfold eqA,Term.eqA; intros; subst; trivial. Qed.

  Lemma IN_eqA_compat : forall ss x x', In x' ss -> x =A= x' -> In x ss.

  Proof. unfold eqA,Term.eqA; intros; subst; trivial. Qed.

(***********************************************************************)
(** inductive predicate saying when a variable occurs in a term *)

  Inductive in_term_vars : variable -> term -> Prop :=
  | is_var : forall x, in_term_vars x (Var x)
  | is_in_list : forall x f ss,
    ex (fun s => In s ss /\ in_term_vars x s) -> in_term_vars x (Fun f ss).

(***********************************************************************)
(** basic properties *)

  Lemma var_in : forall x t, lt_mpo (Var x) t -> in_term_vars x t.

  Proof.
    intros x t; induction t as [y| f ts IHt] using term_ind_forall2; intro H;
      inversion H; subst.
    elim H2; clear H2; intros t Ht; elim Ht; clear Ht; intros t_in_ts Ht.
    constructor; exists t; split; trivial.
    elim Ht; clear Ht; intro Ht.
    (* case t = x : *)
    subst; constructor.
    (* case x < t : *)
    apply IHt; trivial.
  Qed.

  Lemma in_var : forall x t, in_term_vars x t -> le_mpo (Var x) t.

  Proof.
    intros x t; induction t as [y| f ts IHt] using term_ind_forall2; intro H;
      inversion H; subst.
    left; trivial.
    elim H2; clear H2; intros s Hs; elim Hs; clear Hs; intros s_in_ss Hs.
    right; constructor 3; exists s; split; trivial.
    elim (IHt s s_in_ss Hs); intro caseIHt;
      [left; subst; trivial | right; hyp].
  Qed.

  Lemma strict_subterm_less : forall s f ss, In s ss -> lt_mpo s (Fun f ss).

  Proof.
    intros s f ss Hin. constructor 3. exists s. split; try left; trivial.
  Qed.

  Lemma var_in_s_in_terms_greater_than_s : forall t s, le_mpo t s -> 
    forall x, in_term_vars x t -> in_term_vars x s.

  Proof.
    intros t s H; elim H; clear H; intro H.
    subst t; trivial.
    revert s H.
    induction t as [x | g ts HInd1] using term_ind_forall2.
    (* case t  = var x *)
    intros s Hts x0 Hx0.
    (* Hx0 says x0 is in vars x, so x = x0 *) 
    inversion Hx0.
    subst.
    inversion Hts; subst.
    elim H; clear H; intros s Hs; elim Hs; clear Hs; intros s_in_ss Hss.
    apply var_in; trivial.
    (* case t = g ts *) 
    induction s as [x | f ss HInd2] using term_ind_forall2.
    (* case s = Var x : t <= s imposible *)
    intro Hst; inversion Hst.
    (* case s = f ss *)
    intros Hts x x_in_t.
    inversion Hts as [f' g' ss' ts' ltFfg H H' 
      | f' ss' ts' Hss'ts'  
      | f' ss' t' Hex]; subst.
    (* t < s via mpo1 : *)
    inversion x_in_t; subst.
    elim H2; clear H2; intros tx H2.
    elim H2; clear H2; intros tx_in_ts Htx.
    apply (HInd1 tx tx_in_ts (Fun f ss) (H tx tx_in_ts) x Htx).
    (* t < s via mpo2 : *)
    inversion x_in_t; subst.
    elim H1; clear H1; intros tx H1.
    elim H1; clear H1; intros tx_in_ts Htx.
    apply (HInd1 tx tx_in_ts (Fun f ss)); trivial.
    elim (mult2element (transp lt_mpo) IN_eqA_compat ts ss Hss'ts' tx tx_in_ts).
    intros s Hs; elim Hs; clear Hs; intros s_in_ss Hs.
    constructor 3.
    exists s; split; trivial.
    (* t < s via mpo3 : *)
    elim Hex; clear Hex; intros sx Hex.
    elim Hex; clear Hex; intros sx_in_ss Hsx.
    elim Hsx; clear Hsx; intro Hsx.
    (* case sx = t : *)
    constructor.
    exists sx.
    subst sx; split; trivial.
    (* case t < sx *)
    constructor.
    exists sx.
    split; [hyp | apply (HInd2 sx sx_in_ss Hsx x x_in_t)].
  Qed.

  Lemma var_cant_be_greater_than_another_term : forall x t,
    lt_mpo t (Var x) -> False.

  Proof. intros x t mpo_t_var_x. inversion mpo_t_var_x. Qed.

(***********************************************************************)
(** transitivity *)

  Lemma transitive_lt_mpo : forall u t s : term,
    lt_mpo u t -> lt_mpo t s -> lt_mpo u s. 

  Proof.
    intro u; induction u as [x | h us HInd1] using term_ind_forall2.
    (* case u variable : *)
    intros t s H1 H2.
    (* case u < t : *)
    inversion H1 as [ |  |x' g ts H eq1 eq2]; subst.
    elim H; clear H; intros t Ht; elim Ht; clear Ht; intros t_in_ts Ht.
    cut (le_mpo (Var x) s);
      [intro H ; elim H; clear H; intro H; trivial | idtac].
    subst; inversion H2.
    (* x <= s : *)
    apply in_var.
    apply (var_in_s_in_terms_greater_than_s (Fun g ts) s); try right; trivial.
    exists t; split; trivial.
    elim Ht; clear Ht; intro Ht; [subst; constructor | apply var_in; trivial].
    (* case u = (h us) *)
    intro t; induction t as [x | g ts HInd2] using term_ind_forall2.
    (* case t variable : u < t imposible *)
    intros t H1; inversion H1.
    (* case t = (g ts) *)
    intro s; induction s as [x | f ss HInd3] using term_ind_forall2.
    (* case s variable : t < s imposible *)
    intros H1 H2; inversion H2.
    (* case s = (f ss) *)
    intros H1 H2.
    inversion H1 as [f' g' ss' ts' ltFfg Hsi 
      | f' ss' ts' Hss'ts' Hsi  
      | f' ss' t' Hex]; subst.
    (* case u < t via mpo1 : *)
    inversion H2 as [g' h' ts' us' ltFgh Hti
      | g' ts' us' Hts'us' Hti
      | g' ts' u' Hex]; subst.
    (* case t < s via mpo1 : *)
    apply mpo1.	
    (* f < h : *) 
    apply ltF_trans with g; hyp.
    (* ui < s : *)
    intros u u_in_us.
    apply (HInd1 u u_in_us (Fun g ts)).
    apply (Hsi u u_in_us).
    hyp.
    (* case t < s via mpo2 : *)
    apply mpo1.		
    (* f < h : *)
    hyp.
    (* u < s  : *)
    intros u u_in_us.
    apply (HInd1 u u_in_us (Fun f ts)).
    apply (Hsi u u_in_us).
    hyp.
    (* case t < s via mpo3 : *)
    elim Hex; intros s Hs2; elim Hs2; clear Hs2; intros s_in_ss Hs2.
    gen (HInd3 s s_in_ss); intro HInd3'.
    apply (mpo3 (Fun h us) f ss).
    exists s.
    split; trivial.
    right.
    elim Hs2; clear Hs2; intro Hs2.
    (* case s = g ts : *)
    subst s; hyp.
    (* case g ts < s : *)
    apply HInd3'; hyp.
    (* case u < t via mpo2 : *)
    gen (mult2element (transp lt_mpo) IN_eqA_compat us ts Hss'ts');
    intro Hss.
    inversion H2 as [g' h' ts' us' ltFgh Hti
      | g' ts' us' Hts'us' Hti
      | g' ts' us' Hex]; subst.
    (* case t < s via mpo1 : *)
    apply mpo1.
    (* g < h : *)
    hyp.
    (* u < s : *)
    intros u u_in_us.
    apply (HInd1 u u_in_us (Fun g ts)); trivial.
    elim (Hss u u_in_us).
    intros t Ht; elim Ht; clear Ht; intros t_in_ts Ht.
    apply mpo3.
    exists t.
    split; trivial.
    (* case t < s via mpo2 : *)
    apply mpo2.
    (* mult lt_mpo us ss : *)
      apply transp_trans_to_mult_trans with ts; trivial.
    apply tlt_mpo_eqA_compat.
    (* case t < s via mpo3 : *)
    elim Hex; clear Hex; intros s Hs2; elim Hs2; clear Hs2; intros s_in_ss Hs2.
    gen (HInd3 s s_in_ss H1); intro HInd3'.
    apply (mpo3 (Fun g us) f ss).
    exists s.
    split; trivial.
    right.
    elim Hs2; clear Hs2; intro Hs2.
    (* case s = g ts : *)
    subst s; hyp.
    (* case g ts < s : *)
    apply HInd3'; hyp.
    (* case u < t via mpo3 : *)
    elim Hex; clear Hex; intros ti Hti; elim Hti; clear Hti;
      intros ti_in_ts Hti.
    inversion H2 as [g' h' ts' us' ltFgh Hti'
      | g' ts' us' Hts'us' Hti'
      | g' ts' us' Hex]; subst.
    (* case t < s via mpo1 : *)
    elim Hti; clear Hti; intro Hti.
    rewrite <- Hti; apply (Hti' ti ti_in_ts).
    apply (HInd2 ti ti_in_ts (Fun f ss) Hti).
    apply (Hti' ti ti_in_ts).
    (* case t < s via mpo2 : *)
    elim Hti; clear Hti; intro Hti.
    rewrite <- Hti; elim
      (mult2element (transp lt_mpo) IN_eqA_compat ts ss Hts'us' ti ti_in_ts).
    intros x Hx; elim Hx; clear Hx; intros x_in_ss Hx.
    apply mpo3.
    exists x; split; trivial.
    apply (HInd2 ti ti_in_ts (Fun f ss)); trivial.
    elim (mult2element (transp lt_mpo) IN_eqA_compat ts ss Hts'us' ti ti_in_ts).
    intros x Hx; elim Hx; clear Hx; intros x_in_ss Hx.
    apply mpo3.
    exists x; split; trivial.
    (* case t < s via mpo3 : *)
    elim Hex; clear Hex; intros s Hs2; elim Hs2; clear Hs2; intros s_in_ss Hs2.
    apply mpo3.
    exists s.
    split; trivial.
    elim Hs2; clear Hs2; intro Hs2.
    subst s; right; hyp.
    right; apply (HInd3 s s_in_ss); trivial.
  Qed.

  Lemma transitive_le_mpo : transitive le_mpo.

  Proof.
    intros s t u MPOst MPOtu; elim MPOst; clear MPOst; intro MPOst.
    subst t; hyp.
    elim MPOtu; clear MPOtu; intro MPOtu.
    subst t; right; hyp.
    right; apply transitive_lt_mpo with t; hyp.
  Qed.

(***********************************************************************)
(** preservation of irreflexivity *)

  Lemma irreflexive_lt_mpo : irreflexive ltF -> irreflexive lt_mpo.

  Proof.
    intro ltF_irrefl.
    intros s; induction s as [x | f ss IHs] using term_ind_forall2;
      intro H; inversion H; subst.
    (* case mpo1 : *)
    apply (ltF_irrefl f); trivial.
    (* case mpo2 : *)
    gen H1; apply irrefl_to_mult_irrefl.
    unfold eqA,Term.eqA; intros; subst; trivial.
    unfold eqA,Term.eqA; intros; subst; trivial.
    intros x y z; unfold transp; simpl; intros; apply
      transitive_lt_mpo with y; trivial.
    unfold transp; simpl; intros s s_in_ss Hs; apply (IHs s); trivial.
    (* case mpo3 : *)
    elim H2; intros s Hs; elim Hs; clear Hs; intros s_in_ss Hs.
    elim Hs; clear Hs; intro case_s.
    apply (IHs s); subst; trivial.
    apply (IHs s s_in_ss).
    apply transitive_lt_mpo with (Fun f ss); trivial.
    constructor 3; exists s; split; trivial; left; trivial.
  Qed.

(***********************************************************************)
(** well-foundedness *)

  Lemma Acc_lt_mpo_var : forall x, Acc lt_mpo (Var x).

  Proof.
    intro x; constructor; intros t lt_mpo_t_var_x.
    elim (var_cant_be_greater_than_another_term x t); hyp.
  Qed.

  Lemma wf_lt_mpo : well_founded lt_mpo.

  Proof.
    intro s; induction s as [ | f ss HInd1] using term_ind_forall2.
    (* case s variable : *)
    apply Acc_lt_mpo_var.
    (* case s = f ss : *)
    revert ss HInd1.
    induction (wf_ltF f) as [f acc_f HInd2].
    intros ss HInd3; cut (Acc (mult (transp lt_mpo)) ss).
    intro Acc_ss; gen HInd3; clear HInd3.
    induction Acc_ss as [ss Acc_ss HInd3]. 
    constructor; intro t;
      induction t as [ | g ts HInd4] using term_ind_forall2; intro H.
    (* case t variable : *)
    apply Acc_lt_mpo_var.
    (* case t = g ts : *)
    inversion H as [f' g' ss' ts' ltFfg Hsi'
      | f' ss' ts' Hss'ts' Hsi'
      | f' s' ts' Hex]; subst.
    (* case t < s via mpo1 : *)
    apply (HInd2 g ltFfg ts).
    (* all terms in ts are accesible : *)
    intros t t_in_ts.
    apply (HInd4 t t_in_ts).
    apply (Hsi' t t_in_ts).
    (* case t < s via mpo2 : *)
    cut (forall t : term, In t ts -> Acc lt_mpo t);
      [intro acc_t | intros t t_in_ts].
    apply (HInd3 ts); try hyp. (*Hind3*)
    (* all terms in ts are accesible : *)
    apply (HInd4 t t_in_ts). (*Hind4*)
    apply transitive_lt_mpo with (Fun f ts); trivial.
    apply strict_subterm_less; hyp.
    (* case t < s via mpo3 : *)
    elim Hex; clear Hex; intros s Hs; elim Hs; clear Hs; intros s_in_ss MPO_s_t.
    gen (HInd0 s s_in_ss); intro Acc_s.
    elim MPO_s_t; [intro; subst s; trivial | gen (Fun g ts)].
    inversion Acc_s; hyp.
    apply
      (HAccTermsToTermlist (transp lt_mpo) tlt_mpo_eqA_compat IN_eqA_compat).
    intros s s_in_ss; gen (HInd3 s s_in_ss). rewrite transp_invol. auto.
  Qed.

End Make.
