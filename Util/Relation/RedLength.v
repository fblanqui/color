(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

maximal reduction length of a term
for a finitely branching well-founded relation
*)

Set Implicit Arguments.

From CoLoR Require Import SN ListMax RelUtil ListUtil LogicUtil.
From Stdlib Require Import Arith.

Section S.

Variables (A : Type) (R : relation A) (FB : finitely_branching R) (WF : WF R).

Definition len_aux x (len : forall y, R x y -> nat) :=
  let f i (hi : i < length (sons FB x)) :=
    len (ith hi) (in_sons_R FB (ith_In hi))
  in S (lmax (pvalues f)).

Lemma len_aux_ext : forall x (f g : forall y, R x y -> nat),
  (forall y (p : R x y), f y p = g y p) -> len_aux f = len_aux g.

Proof.
intros. unfold len_aux. apply (f_equal (fun l => S (lmax l))).
apply pvalues_eq. intros. apply H.
Qed.

Definition len : A -> nat := Fix (WF_wf_transp WF) _ len_aux.

Lemma len_eq : forall x, len x = S (lmax (map len (sons FB x))).

Proof.
intro. unfold len. rewrite Fix_eq. 2: exact len_aux_ext. fold len.
unfold len_aux. apply (f_equal (fun l => S (lmax l))).
rewrite <- (@pvalues_ith_eq_map A nat). apply pvalues_eq. intros. refl.
Qed.

Lemma R_len : forall x y, R x y -> len x > len y.

Proof.
intros. rewrite len_eq. unfold gt, lt. apply le_n_S. apply in_lmax.
apply in_map. apply R_in_sons. exact H.
Qed.

End S.
