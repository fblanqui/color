(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Model of RPO with status
*)

(* $Id: VRPO_Status.v,v 1.3 2007-05-25 16:22:34 blanqui Exp $ *)

Require Export VPrecedence.
Require Export MultisetListOrder.

Module LMO := MultisetListOrder Term.
Export LMO.

Require Export LexicographicOrder.

Module LO := LexOrder Term.
Export LO.

Inductive status_name : Set := 
  | lexicographic : status_name 
  | multiset : status_name.
  
Variable status : Sig -> status_name.

Definition mytau f (r : relation term) : relation terms := 
  match status f with 
    | lexicographic => lex r
    | multiset => mult (transp r)
  end.

Hypothesis eq_st : forall f g, f =F= g -> status f = status g.
Hypothesis wf_ltF : well_founded ltF.

Inductive lt_rpo : relation term :=
  | rpo1 : forall f g ss ts, g <F f -> 
    (forall t, In t ts -> lt_rpo t (Fun f ss)) -> 
    lt_rpo (Fun g ts) (Fun f ss)
  | rpo2_lex : forall f g, f =F= g -> status f = lexicographic -> 
    forall ss ts, (forall t, In t ts -> lt_rpo t (Fun f ss)) ->       
      lex lt_rpo ts ss -> lt_rpo (Fun g ts) (Fun f ss)
  | rpo2_mult : forall f g, f =F= g -> status f = multiset -> 
    forall ss ts, mult (transp lt_rpo) ts ss -> 
      lt_rpo (Fun g ts) (Fun f ss)
  | rpo3 : forall t f ss, 
    ex (fun s => In s ss /\ (s = t \/ lt_rpo t s)) -> 
    lt_rpo t (Fun f ss).

(***********************************************************************)

Require Export VRPO_Type.

Module RPO_Axioms_Model : RPO_Axioms_Type
  with Definition lt := lt_rpo
    with Definition tau := mytau.

  Definition tau := mytau.

  Lemma status_eq : forall f g, f =F= g -> tau f = tau g.

  Proof.
    intros f g f_eq_g.
    unfold tau, mytau.
    rewrite (eq_st f g f_eq_g).
    trivial.
  Qed.

  Definition lt := lt_rpo.

  (* Verification des axiomes lt : *)
    
  Lemma lt_roots : forall f g, g <F f -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) -> 
      lt (Fun g ts) (Fun f ss).

  Proof.
    intros f g ltgf ss ts Hsub. unfold lt; apply rpo1; trivial.
  Qed.

  Lemma lt_status : forall f g, f =F= g -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) ->       
      tau f lt ts ss -> lt (Fun g ts) (Fun f ss).

  Proof.
    unfold lt, tau, mytau.
    intros f g feqg ss ts Hsub; generalize (refl_equal (status f));
      pattern (status f) at -1;
      case (status f); intros statusf Hstatusf.
    apply rpo2_lex; trivial.
    apply rpo2_mult; trivial.
  Qed.

  Lemma lt_subterm : forall f ss t, 
    ex (fun s => In s ss /\ (s = t \/ lt t s)) -> lt t (Fun f ss).

  Proof.
    intros f ss t Hex; unfold lt; apply rpo3; trivial.
  Qed.
    
  Lemma lt_decomp : forall s t, lt s t -> 
    ((ex (fun f => ex (fun g => ex (fun ss => ex (fun ts => 
      ltF f g /\ 
      (forall s, In s ss -> lt s (Fun g ts)) /\
      s = Fun f ss /\ 
      t = Fun g ts
    )))))
    \/
    ex (fun f => ex (fun g => ex (fun ss => ex (fun ts => 
      f =F= g /\
      (forall s, In s ss -> lt s (Fun g ts)) /\
      tau f lt ss ts /\
      s = Fun f ss /\ 
      t = Fun g ts)))))
    \/
    ex (fun f => ex (fun ts => ex (fun t' =>
      In t' ts /\ (s = t' \/ lt s t')) /\ t = Fun f ts)).

  Proof.
    intros s t Hst.
    unfold lt in Hst; inversion Hst as [f'' g'' ss' ts'' ltFfg Hsi'
      | f'' g'' feq fstat ss' ts'' Hsub Hss'ts' Hsi'
      | f'' g'' feq fstat ss' ts'' Hss'ts' Hsi'
      | f'' s' ts'' Hex]; subst.
    left; left.
    exists g''; exists f''; exists ts''; exists ss'.
    split; trivial; repeat split; trivial.
    left; right.
    exists g''; exists f''; exists ts''; exists ss'.
    split; elim feq; trivial; repeat split; trivial.
    rewrite <- (status_eq f'' g'' feq);
      unfold tau, mytau; rewrite fstat; simpl; trivial.
    left; right.
    exists g''; exists f''; exists ts''; exists ss'.
    split; elim feq; trivial; repeat split; trivial.
    intros s s_in_ts'; apply rpo3; trivial.
    assert (Hcomp : forall ss x x', In x' ss -> x =A= x' -> In x ss).
    unfold Sid.eqA, Term.eqA; intros; subst; trivial.      
    elim (mult2element _ Hcomp  _ _ Hss'ts' s s_in_ts').
    intros s' Hs'.
    exists s'; split; elim Hs'; trivial.
    rewrite <- (status_eq f'' g'' feq);
      unfold tau, mytau; rewrite fstat; simpl; trivial.
    right.
    exists s'; exists ts''.
    split; trivial; elim Hex; clear Hex; intros t Ht.
    elim Ht; clear Ht; intros t_in_ts Ht.
    exists t; split; trivial.
    elim Ht; [left; subst | right]; trivial.
  Qed.

End RPO_Axioms_Model.

(***********************************************************************)

Module RPO_MSO_Model : RPO_MSO_Type with Module Base := RPO_Axioms_Model.

  Module Base := RPO_Axioms_Model.
  Export Base.

  Lemma SPO_to_status_SPO : forall f (r : relation term), forall ss, 
    (forall s, In s ss -> (forall t u, r s t -> r t u -> r s u)
      /\ (r s s -> False)) ->
    (forall ts us, tau f r ss ts -> tau f r ts us -> tau f r ss us)
    /\ (tau f r ss ss -> False).

  Proof.
    intros f r. 
    unfold tau, mytau; destruct (status f); simpl.
    apply SPO_to_lex_SPO.
    intros.
    apply transp_SPO_to_mult_SPO; trivial.
    unfold Sid.eqA, Term.eqA; intros; subst; trivial.
    unfold Sid.eqA, Term.eqA; intros; subst; trivial.
  Qed.

  Lemma mono_axiom : forall f (r : relation term), 
    forall ss ts, one_less r ss ts -> (tau f r) ss ts.

  Proof.
    intros f r ss ts.
    unfold tau, mytau; destruct (status f); simpl.
    apply one_less2lex.
    apply one_less2mult.
    unfold Sid.eqA, Term.eqA; intros; subst; trivial.
  Qed.  

End RPO_MSO_Model.

(***********************************************************************)

Module RPO_Wf_Model : RPO_Wf_Type with Module Base := RPO_Axioms_Model.

  Module Base := RPO_Axioms_Model.
  Export Base.

  Definition wf_ltF := wf_ltF.

  Definition lifting (R : relation terms) := 
    forall l, accs lt l ->  Restricted_acc (accs lt) R l.
        
  Lemma status_lifting : forall f, lifting (tau f lt).

  Proof.
    intro f; unfold tau, mytau, lt.
    intro l; destruct (status f).
    apply (lex_lifting lt_rpo).
    apply (mult_lifting lt_rpo).
    unfold Sid.eqA, Term.eqA; intros; subst; trivial.
    unfold Sid.eqA, Term.eqA; intros; subst; trivial.
  Qed.
  
End RPO_Wf_Model.
