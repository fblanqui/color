(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-25

well-founded monotone interpretations
************************************************************************)

(* $Id: AWFMInterpretation.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

Require Export AInterpretation.
Require Export WfUtil.

Record WFMinterpretation : Type := mkWFMInterpretation {
  WFMI :> interpretation Sig;
  WFMI_a : domain WFMI;
  WFMI_R : relation (domain WFMI);
  WFMI_wf : wf WFMI_R;
  WFMI_mon : forall f, Vmonotone (fint WFMI f) WFMI_R
}.

(***********************************************************************)
(* ordering on terms *)

Variable W : WFMinterpretation.

Definition WFMI_R' t1 t2 :=
  forall xint, WFMI_R W (term_int xint t1) (term_int xint t2).

(***********************************************************************)
(* substitution lemma *)

Require Export ASubstitution.

Definition beta (xint : valuation W) (s : substitution Sig) :=
  fun x => term_int xint (s x).

Lemma substitutionLemma : forall xint s t,
  term_int xint (app s t) = term_int (beta xint s) t.

Proof.
intros xint s t. pattern t.
eapply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (term_int xint) (Vmap (app s) ts) = Vmap (term_int (beta xint s)) ts).
intro x. simpl. reflexivity.
intros f ts.
rewrite term_int_fun. rewrite app_fun. rewrite term_int_fun.
intro H. apply (f_equal (fint W f)). assumption.
simpl. reflexivity.
intros. simpl. rewrite H. rewrite <- H0. reflexivity.
Qed.

Require Export ARelation.

(***********************************************************************)
(* R' is a reduction ordering *)

Lemma WFMI_R'_is_redOrder : reduction_ordering WFMI_R'.

Proof.
split; [idtac | split].

(* Proof of well-foundedness *)
apply wf_incl with (R2 :=
  let xint := fun t => WFMI_a W in fun t1 t2 =>
  transp (WFMI_R W) (term_int xint t1) (term_int xint t2)).

 unfold transp, WFMI_R'. unfold inclusion. auto.
 unfold WFMI_R'. apply wf_inverse_image
 with (f := (term_int (fun t => WFMI_a W))).
 exact (WFMI_wf W).

(* Proof of closure under substitution *)
unfold transp, substitution_closed, WFMI_R'.
intros t1 t2 s H xint0.
do 2 rewrite substitutionLemma.
apply (H (beta xint0 s)).

(* Proof of closure under context *)
unfold transp, context_closed, WFMI_R'.
intros t1 t2 c H xint0. generalize (H xint0). clear H. intro H.
induction c.
simpl. assumption.
simpl fill. do 2 rewrite term_int_fun.
do 2 (rewrite Vmap_cast; rewrite Vmap_app).
simpl. apply (WFMI_mon W). assumption.
Qed.

End S.
