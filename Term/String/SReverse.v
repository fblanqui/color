(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-04

string reversing

Termination of String Rewriting Proved Automatically, H. Zantema,
Journal of Automated Reasoning, 2005, volume 34, pages 105-139
*)

Set Implicit Arguments.

From CoLoR Require Import Srs ListUtil RelUtil LogicUtil.

Section S.

Variable Sig : Signature.

Definition reverse (e : rule Sig) := let (l,r) := e in mkRule (rev' l) (rev' r).

Notation reverses := (List.map reverse).

Lemma red_rev : forall R t u, red R t u -> red (reverses R) (rev' t) (rev' u).

Proof.
intros. redtac. unfold fill. rewrite !rev'_app, !app_ass.
ex (rev' l) (rev' r) (mkContext (rev' (rgt c)) (rev' (lft c))). intuition.
change (In (reverse (mkRule l r)) (reverses R)). apply in_map. exact H.
Qed.

Lemma red_rev_rtc : forall E t u,
  red E # t u -> red (reverses E) # (rev' t) (rev' u).

Proof.
intros. elim H; intros. apply rt_step. apply red_rev. exact H0.
apply rt_refl. eapply rt_trans. apply H1. exact H3.
Qed.

Lemma red_mod_rev : forall E R t u,
  red_mod E R t u -> red_mod (reverses E) (reverses R) (rev' t) (rev' u).

Proof.
intros. redtac. exists (rev' (fill c l)). split. apply red_rev_rtc. exact H.
apply red_rev. exists l. exists r. exists c. auto.
Qed.

From CoLoR Require Import SN.

Lemma WF_red_mod_rev : forall E R,
  WF (red_mod (reverses E) (reverses R)) -> WF (red_mod E R).

Proof.
unfold WF. intros E R H. cut (forall x, SN (red_mod E R) (rev' x)).
intros. ded (H0 (rev' x)). rewrite rev'_rev' in H1. exact H1.
intro. ded (H x). elim H0. intros. apply SN_intro. intros.
ded (H2 (rev' y)). rewrite rev'_rev' in H4. apply H4.
ded (red_mod_rev H3). rewrite rev'_rev' in H5. exact H5.
Qed.

Lemma reverse_reverse : forall a, reverse (reverse a) = a.

Proof.
intros [l r]. unfold reverse. rewrite !rev'_rev'. refl.
Qed.

Lemma reverses_reverses : forall R, reverses (reverses R) = R.

Proof.
intro. rewrite map_map. apply map_eq_id. intros. apply reverse_reverse.
Qed.

Lemma WF_red_mod_rev_eq : forall E R,
  WF (red_mod (reverses E) (reverses R)) <-> WF (red_mod E R).

Proof.
split; intro. apply WF_red_mod_rev. hyp. apply WF_red_mod_rev.
rewrite !reverses_reverses. hyp.
Qed.

Lemma WF_red_rev_eq : forall R, WF (red (reverses R)) <-> WF (red R).

Proof.
intro. rewrite <- !red_mod_empty.
assert (nil = reverses nil). refl. rewrite H. apply WF_red_mod_rev_eq.
Qed.

End S.

(***********************************************************************)
(** tactics for Rainbow *)

Ltac rev_tac := rewrite <- WF_red_rev_eq || rewrite <- WF_red_mod_rev_eq.
