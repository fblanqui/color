(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Model of LPO statisfying Hypotheses in RPO_Types
*)

From CoLoR Require Import VPrecedence ListLex VRPO_Type VTerm ListUtil AccUtil
  LogicUtil.
From Stdlib Require Import Relations.

Module LPO (PT : VPrecedenceType).

  Module Export P := VPrecedence PT.
  Module Export S := Status PT.

  Inductive lt_lpo : relation term :=
    | lpo1 : forall f g ss ts, g <F f -> 
        (forall t, In t ts -> lt_lpo t (Fun f ss)) -> 
        lt_lpo (Fun g ts) (Fun f ss)
    | lpo2 : forall f g, f =F= g -> forall ss ts,
        (forall t, In t ts -> lt_lpo t (Fun f ss)) ->       
        lex lt_lpo ts ss -> lt_lpo (Fun g ts) (Fun f ss)
    | lpo3 : forall t f ss, 
        ex (fun s => In s ss /\ (s = t \/ lt_lpo t s)) ->
        lt_lpo t (Fun f ss).

  Definition mytau (f : Sig) (r : relation term) := lex r.

End LPO.

(***********************************************************************)

From CoLoR Require Import VRPO_Type.

Module LPO_Model (PT : VPrecedenceType) <: RPO_Model with Module P := PT.

  Module P := PT.
  Module Export LPO := LPO PT.
    
  Definition tau := mytau.

  Lemma tau_dec : forall f R ts ss,
    (forall t s, In t ts -> In s ss -> {R t s} + {~R t s}) ->
    {tau f R ts ss} + {~tau f R ts ss}.

  Proof.
    unfold tau, mytau. intros. apply lex_status_dec. hyp.
  Defined.

  Lemma status_eq : forall f g, f =F= g -> tau f = tau g.

  Proof.
    auto.
  Qed.

  Definition lt := lt_lpo.

  (* Verification des axiomes lt : *)
    
  Lemma lt_roots : forall f g, g <F f -> forall ss ts,
    (forall t, In t ts -> lt t (Fun f ss)) -> lt (Fun g ts) (Fun f ss).

  Proof.
    intros f g ltgf ss ts Hsub. unfold lt; apply lpo1; trivial.
  Qed.
      
  Lemma lt_status : forall f g, f =F= g -> 
    forall ss ts, (forall t, In t ts -> lt t (Fun f ss)) ->       
      tau f lt ts ss -> lt (Fun g ts) (Fun f ss).

  Proof.
    unfold lt, tau, mytau. intros f g feqg ss ts Hsub. apply lpo2; trivial.
  Qed.

  Lemma lt_subterm : forall f ss t, 
    ex (fun s => In s ss /\ (s = t \/ lt t s)) -> lt t (Fun f ss).

  Proof.
    intros f ss t Hex; unfold lt; apply lpo3; trivial.
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
      | f'' g'' feq ss' ts'' Hsub Hss'ts' Hsi'
      | f'' s' ts'' Hex]; subst.
    left; left.
    exists g''; exists f''; exists ts''; exists ss'.
    split; trivial; repeat split; trivial.
    left; right.
    exists g''; exists f''; exists ts''; exists ss'.
    split; elim feq; trivial; repeat split; trivial.
    right.
    exists s'; exists ts''.
    split; trivial; elim Hex; clear Hex; intros t Ht.
    elim Ht; clear Ht; intros t_in_ts Ht.
    exists t; split; trivial.
    elim Ht; [left; subst | right]; trivial.
  Qed.

(***********************************************************************)

  Lemma SPO_to_status_SPO : forall f (r : relation term), 
    forall ss, 
      (forall s, In s ss ->
	(forall t u, r s t -> r t u -> r s u) /\ (r s s -> False)) ->
      (forall ts us, tau f r ss ts -> tau f r ts us -> tau f r ss us)
      /\ (tau f r ss ss -> False).

  Proof.
    intros f r. unfold tau, mytau. apply SPO_to_lex_SPO.
  Qed.
    
  Lemma mono_axiom : forall f (r : relation term),
    forall ss ts, one_less r ss ts -> tau f r ss ts.

  Proof.
    intros f r ss ts. unfold tau, mytau. apply one_less2lex.
  Qed.

(***********************************************************************)

  Definition wf_ltF := ltF_wf.
  Definition leF_dec := leF_dec.

  Definition lifting R := forall l, Accs lt l ->  Restricted_acc (Accs lt) R l.

  Lemma status_lifting : forall f, lifting (tau f lt).

  Proof.
    intro f; unfold tau, mytau, lt, lifting. apply (lex_lifting lt_lpo).
  Qed.

End LPO_Model.
