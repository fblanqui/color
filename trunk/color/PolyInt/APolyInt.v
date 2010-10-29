(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2004-12-13
- Adam Koprowski, 2007-04-26 (modular removal of rules) 
                  2008-05-27 (weakly monotone polynomials)

proof of the termination criterion based on polynomial interpretations
*)

Set Implicit Arguments.

Require Import ATerm.
Require Import ABterm.
Require Import ListUtil.
Require Import ListForall.
Require Import VecUtil.
Require Import PositivePolynom.
Require Import AInterpretation.
Require Import ZUtil.
Require Import NaryFunction.
Require Import ARelation.
Require Import RelUtil.
Require Import LogicUtil.
Require Import SN.
Require Import Polynom.
Require Import MonotonePolynom.
Require Import NatUtil.

Section S.

Variable Sig : Signature.

Notation bterm := (bterm Sig).

Definition PolyInterpretation := forall f : Sig, poly (arity f).

(***********************************************************************)
(** polynomial associated to a bterm *)

Section pi.

Variable PI : PolyInterpretation.

Fixpoint termpoly k (t : bterm k) {struct t} : poly (S k) :=
  match t with
    | BVar x H => ((1)%Z, mxi (gt_le_S (le_lt_n_Sm H))) :: nil
    | BFun f v => pcomp (PI f) (Vmap (@termpoly k) v)
  end.

(***********************************************************************)
(** monotony properties *)

Definition PolyWeakMonotone := forall f : Sig, pweak_monotone (PI f).
Definition PolyStrongMonotone := forall f : Sig, pstrong_monotone (PI f).

Section fin_Sig.

  Variable Fs : list Sig.
  Variable Fs_ok : forall f : Sig, In f Fs.

  Lemma fin_PolyWeakMonotone :
    forallb (fun f => bpweak_monotone (PI f)) Fs = true -> PolyWeakMonotone.

  Proof.
    rewrite forallb_forall. intros H f. rewrite <- bpweak_monotone_ok.
    apply H. apply Fs_ok.
  Qed.

End fin_Sig.

(***********************************************************************)
(** coefficients are positive *)

Variable PI_WM : PolyWeakMonotone.
Variable PI_SM : PolyStrongMonotone.

Section coef_pos.

Let P := fun (k : nat) (t : bterm k) => coef_pos (termpoly t).
Let Q := fun (k n : nat) (ts : vector (bterm k) n) => Vforall (@P k) ts.

Lemma bterm_poly_pos : forall (k : nat) (t : bterm k), P t.

Proof.
intros k t. apply (bterm_ind (@P k) (@Q k)).
 intros v Hv. unfold P. simpl. intuition.
 unfold Q. intros f ts H. unfold P. simpl.
 apply coef_pos_pcomp.
  apply (PI_WM f).
  unfold P in H. apply Vforall_map_intro. auto.
 unfold Q. simpl. trivial.
 intros t' n' s' H1. unfold Q. intro H2. simpl. split; assumption.
Qed.

End coef_pos.

(***********************************************************************)
(** interpretation in D *)

Definition Int_of_PI := mkInterpretation D0 (fun f => peval_D (PI_WM f)).

Let I := Int_of_PI.

(***********************************************************************)
(** interpretation monotony *)

Require Import AWFMInterpretation.

Lemma pi_monotone : monotone I Dgt.

Proof.
intro f. unfold Dgt. apply Vmonotone_transp.
apply (pmonotone_imp_monotone_peval_Dlt (proj1 (PI_SM f)) (PI_SM f)).
Qed.

Lemma pi_monotone_eq : monotone I Dge.

Proof.
intro f. unfold Dge. apply Vmonotone_transp.
apply (coef_pos_monotone_peval_Dle (PI_WM f)).
Qed.

(***********************************************************************)
(** reduction ordering *)

Let succ := IR I Dgt.

Lemma pi_red_ord : reduction_ordering succ.

Proof.
unfold succ. apply IR_reduction_ordering. apply pi_monotone. apply WF_Dgt.
Qed.

(***********************************************************************)
(** reduction pair *)

Let succ_eq := IR I Dge.

Lemma pi_absorb : absorb succ succ_eq.

Proof.
unfold absorb, inclusion. intros. do 2 destruct H.
unfold succ_eq, succ, IR, Dge, Dgt, transp, Dle, Dlt in *. intro.
eapply Zlt_le_trans. apply H0. apply H.
Qed.

Definition rp := @mkReduction_pair Sig
  (*rp_succ : relation term;*)
  succ
  (*rp_succ_eq : relation term;*)
  succ_eq
  (*rp_subs : substitution_closed rp_succ;*)
  (@IR_substitution_closed _ I Dgt)
  (*rp_subs_eq : substitution_closed rp_succ_eq;*)
  (@IR_substitution_closed _ I Dge)
  (*rp_cont : context_closed rp_succ;*)
  (@IR_context_closed _ _ _ pi_monotone)
  (*rp_cont_eq : context_closed rp_succ_eq;*)
  (@IR_context_closed _ _ _ pi_monotone_eq)
  (*rp_absorb : absorb rp_succ rp_succ_eq;*)
  pi_absorb
  (*rp_succ_wf : WF rp_succ*)
  (@IR_WF _ I _ WF_Dgt).

(***********************************************************************)
(** equivalence between (xint) and (vec_of_val xint) *)

Let f1 (xint : valuation I) k (t : bterm k) := proj1_sig (bterm_int xint t).

Let f2 (xint : valuation I) k (t : bterm k) :=
  proj1_sig (peval_D (bterm_poly_pos t) (vec_of_val xint (S k))).
  
Let P (xint : valuation I) k (t : bterm k) := f1 xint t = f2 xint t.

Let Q (xint : valuation I) k n (ts : vector (bterm k) n) :=
  Vforall (@P xint k) ts.

Lemma termpoly_v_eq_1 : forall x k (H : (x<=k)%nat),
  termpoly (BVar H) = (1%Z, mxi (gt_le_S (le_lt_n_Sm H))) :: pzero (S k).

Proof.
intros. simpl. refl.
Qed.

Lemma termpoly_v_eq_2 :
  forall x k (H : (x<=k)%nat) (v : vector Z (S k)),
  peval (termpoly (BVar H)) v = meval (mxi (gt_le_S (le_lt_n_Sm H))) v.

Proof.
intros x k H v. rewrite termpoly_v_eq_1. unfold pzero. unfold peval at 1.
ring.
Qed.

Lemma PI_bterm_int_eq : forall xint k (t : bterm k), P xint t.

Proof.
 intros xint k t. apply (bterm_ind (@P xint k) (@Q xint k)).
 intros v Hv. unfold P, f1, f2. simpl bterm_int.
 rewrite val_peval_D.
 rewrite termpoly_v_eq_2.
 rewrite meval_xi. rewrite Vnth_map.
 pattern (xint v) at 1.
 rewrite <- (Vnth_vec_of_val xint (gt_le_S (le_lt_n_Sm Hv))).
 reflexivity.

 intros f ts. unfold Q. intro H. unfold P, f1, f2.
 simpl bterm_int. rewrite val_peval_D. simpl.
 unfold P in H.
 generalize (Vmap_eq H). intro H'.
 rewrite peval_comp.
 apply (f_equal (peval (PI f))).
 rewrite Vmap_map. rewrite Vmap_map.
 unfold f1 in H'. unfold f2 in H'. assumption.

 unfold Q, P. simpl. trivial.

 intros t' n' ts' H1 H2. unfold Q. simpl.
 intuition.
Qed.

Lemma PI_term_int_eq : forall (xint : valuation I) t k 
  (H : (maxvar t <= k)%nat),
  proj1_sig (term_int xint t)
  = proj1_sig (peval_D (bterm_poly_pos (inject_term H))
    (vec_of_val xint (S k))).

Proof.
intros xint t k H. rewrite <- (term_int_eq_bterm_int xint H).
generalize (PI_bterm_int_eq xint (inject_term H)). intuition.
Qed.

Implicit Arguments PI_term_int_eq [t k].

(***********************************************************************)
(** polynomial associated to a rule *)

Require Import ATrs.
Require Import Max.

(* TODO Temporarily introducing some notations for the following 2 definitions,
   for the paper.
   They should be extended and used more consistently in all polynomial-related
   definitions.
 *)

Infix "+" := pplus : poly_scope.
Notation "- y" := (popp y) : poly_scope.
Notation "x - y" := (x + (- y))%poly : poly_scope.
Notation "'0'" := (pconst _ 0) : poly_scope.
Notation "'1'" := (pconst _ 1) : poly_scope.

Bind Scope poly_scope with poly.
Open Scope poly_scope.

Hint Unfold maxvar_le.
Hint Resolve le_max_l le_max_r.

Program Definition rulePoly_ge rule := 
  let l := lhs rule in let r := rhs rule in
  let m := max (maxvar l) (maxvar r) in
  termpoly (@inject_term _ m l _) - termpoly (@inject_term _ m r _).

Definition rulePoly_gt rule := rulePoly_ge rule - 1.

(***********************************************************************)
(** compatibility *)

Require Import ZUtil.

Lemma pi_compat_rule : forall r,
  coef_pos (rulePoly_gt r) -> succ (lhs r) (rhs r).

Proof.
intros r H_coef_pos. unfold succ, IR. intro xint. unfold Dgt, Dlt, transp.
set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
rewrite (PI_term_int_eq xint (le_max_r mvl mvr)). do 2 rewrite val_peval_D.
pose (v := (Vmap (proj1_sig (P:=pos)) (vec_of_val xint (S (max mvl mvr))))).
apply pos_lt. rewrite <- (peval_const (1)%Z v). do 2 rewrite <- peval_minus.
unfold v. apply pos_peval. exact H_coef_pos.
Qed.

Lemma pi_compat_rule_weak : forall r,
  coef_pos (rulePoly_ge r) -> succ_eq (lhs r) (rhs r).

Proof.
intros r H_coef_pos. unfold succ_eq, IR. intro xint. unfold Dge, Dle, transp.
set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
rewrite (PI_term_int_eq xint (le_max_r mvl mvr)). 
do 2 rewrite val_peval_D. apply pos_le. rewrite <- peval_minus.
apply pos_peval. exact H_coef_pos.
Qed.

Require Import ACompat.

Lemma pi_compat : forall R,
  lforall (fun r => coef_pos (rulePoly_gt r)) R -> compat succ R.

Proof.
unfold compat. intros. set (rho := mkRule l r).
change (succ (lhs rho) (rhs rho)). apply pi_compat_rule.
apply (lforall_in H H0).
Qed.

(***********************************************************************)
(** termination *)

Require Import AMannaNess.

Lemma polyInterpretationTermination : forall R,
  lforall (fun r => coef_pos (rulePoly_gt r)) R -> WF (red R).

Proof.
intros R H. apply manna_ness with (succ := succ). apply pi_red_ord.
apply pi_compat. exact H.
Qed.

End pi.

(***********************************************************************)
(** default polynomial interpretation *)

Definition default_poly n :=
  List.map (fun x => (1%Z, mxi (prf x))) (nats_lt n).

Lemma coef_default_poly : forall n i (h : i<n),
  coef (mxi h) (default_poly n) = 1%Z.

Proof.
(*TODO*)
Abort.

Definition default_pi (f : Sig) := default_poly (arity f).

Lemma pweak_monotone_default : PolyWeakMonotone default_pi.

Proof.
intro f. unfold pweak_monotone, coef_pos, default_pi. rewrite lforall_eq.
intros. destruct (in_map_elim H). destruct H0. subst. simpl. omega.
Qed.

Lemma pstrong_monotone_default : PolyStrongMonotone default_pi.

Proof.
intro f. unfold pstrong_monotone. split. apply pweak_monotone_default.
intros. (*TODO*)
Abort.

End S.

(***********************************************************************)
(** tactics *)

(*REMOVE: to be removed: tactic used in an old version of Rainbow

Ltac poly_int PI := solve
  [match goal with
    |- WF (red ?R) =>
      apply (polyInterpretationTermination PI R);
	vm_compute; intuition; discriminate
  end] || fail "invalid polynomial interpretation".*)

Ltac PolyWeakMonotone Fs Fs_ok :=
  match goal with
    | |- PolyWeakMonotone ?PI =>
      apply (fin_PolyWeakMonotone PI Fs Fs_ok);
        (check_eq || fail "could not prove monotony")
  end.
