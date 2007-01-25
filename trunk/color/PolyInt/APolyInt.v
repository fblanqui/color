(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-13
- Sebastien Hinderer, 2004-04-20

proof of the termination criterion based on polynomial interpretations
*)

(* $Id: APolyInt.v,v 1.9 2007-01-25 14:50:06 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ABterm.

Notation bterm := (bterm Sig).

(***********************************************************************)
(** polynomial associated to a bterm *)

Section poly_of_bterm.

Require Export Polynom.

Variable fpoly : forall f : Sig, poly (arity f).

Fixpoint termpoly k (t : bterm k) {struct t} : poly (S k) :=
  match t with
    | BVar x H =>
      ((1)%Z, mxi (gt_le_S x (S k) (le_lt_n_Sm x k H))) :: nil
    | BFun f v =>
      let fix tmp n0 (v : vector (bterm k) n0) {struct v}
	: vector (poly (S k)) n0 :=
        match v in vector _ n0 return vector (poly (S k)) n0 with
          | Vnil => Vnil
          | Vcons t' n' v' => Vcons (termpoly t') (tmp n' v')
        end
      in pcomp (fpoly f) (tmp (arity f) v)
  end.

Lemma termpoly_eq :
  forall (k : nat) (f : Sig) (ts : vector (bterm k) (arity f)),
  termpoly (BFun f ts) = pcomp (fpoly f) (Vmap (@termpoly k) ts).

Proof.
intros. simpl termpoly at 1.
apply (f_equal (@pcomp (arity f) (fpoly f) (S k))). elim ts.
auto. intros t' n' ts' Hrec. rewrite Hrec. auto.
Qed.

End poly_of_bterm.

(***********************************************************************)
(** polynomial interpretation *)

Require Export MonotonePolynom.

Record PolyInterpretation : Type := mkPolyInterpretation {
  PI_poly : forall f : Sig, poly (arity f);
  PI_mon : forall f : Sig, pmonotone (PI_poly f)
}.

Variable PI : PolyInterpretation.

(***********************************************************************)
(** coefficients are positive *)

Section coef_pos.

Let P := fun (k : nat) (t : bterm k) => coef_pos (termpoly (PI_poly PI) t).
Let Q := fun (k n : nat) (ts : vector (bterm k) n) => Vforall (@P k) ts.

Lemma bterm_poly_pos : forall (k : nat) (t : bterm k), P t.

Proof.
intros k t. apply (bterm_ind (@P k) (@Q k)).
 intros v Hv. unfold P. simpl. intuition.
 unfold Q. intros f ts H. unfold P. rewrite termpoly_eq.
 apply coef_pos_pcomp.
  apply (proj1 (PI_mon PI f)).
  unfold P in H. apply Vforall_map_intro. auto.
 unfold Q. simpl. trivial.
 intros t' n' s' H1. unfold Q. intro H2. simpl. split; assumption.
Qed.

End coef_pos.

(***********************************************************************)
(** interpretation in D *)

Definition Int_of_PI :=
  mkInterpretation D0 (fun f => peval_D (proj1 (PI_mon PI f))).

Let W := Int_of_PI.

(***********************************************************************)
(** monotony *)

Require Export AWFMInterpretation.

Lemma pi_monotone : monotone W Dgt.

Proof.
intro f. unfold Dgt. apply Vmonotone_transp.
apply (pmonotone_imp_monotone_peval_Dlt (PI_mon PI f)).
Qed.

(***********************************************************************)
(** reduction ordering *)

Definition succ := IR W Dgt.

Lemma pi_red_ord : reduction_ordering succ.

Proof.
unfold succ. apply IR_reduction_ordering. apply pi_monotone. apply WF_Dgt.
Qed.

(***********************************************************************)
(** equivalence between (xint) and (fval xint) *)

Let f1 (xint : valuation W) k (t : bterm k) := proj1_sig (bterm_int xint t).

Let f2 (xint : valuation W) k (t : bterm k) :=
  proj1_sig (peval_D (bterm_poly_pos t) (fval xint (S k))).
  
Let P (xint : valuation W) k (t : bterm k) := f1 xint t = f2 xint t.

Let Q (xint : valuation W) k n (ts : vector (bterm k) n) :=
  Vforall (@P xint k) ts.

Lemma termpoly_v_eq_1 : forall x k (H : x<=k),
  termpoly (PI_poly PI) (BVar H) =
  (1%Z, mxi (gt_le_S x (S k) (le_lt_n_Sm x k H))) :: pzero (S k).

Proof.
intros. simpl. refl.
Qed.

Lemma termpoly_v_eq_2 :
  forall x k (H : x<=k) (v : vector Z (S k)),
  peval (termpoly (PI_poly PI) (BVar H)) v =
  meval (mxi (gt_le_S _ _ (le_lt_n_Sm x k H))) v.

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
 rewrite <- (fval_eq xint (gt_le_S v (S k) (le_lt_n_Sm v k Hv))).
 reflexivity.

 intros f ts. unfold Q. intro H. unfold P, f1, f2.
 rewrite bterm_int_fun. rewrite val_peval_D.
 rewrite termpoly_eq.
 
 unfold P in H.
 generalize (Vmap_eq H). intro H'.
 unfold bterms_int.
 rewrite peval_comp.
 simpl (fint W f). rewrite val_peval_D.
 apply (f_equal (peval (PI_poly PI f))).
 rewrite Vmap_map. rewrite Vmap_map.
 unfold f1 in H'. unfold f2 in H'. assumption.

 unfold Q, P. simpl. trivial.

 intros t' n' ts' H1 H2. unfold Q. simpl.
 intuition.
Qed.

Lemma PI_term_int_eq : forall (xint : valuation W) t k (H : maxvar t <= k),
  proj1_sig (term_int xint t)
  = proj1_sig (peval_D (bterm_poly_pos (inject_term H)) (fval xint (S k))).

Proof.
intros xint t k H. rewrite <- (term_int_eq_bterm_int xint H).
generalize (PI_bterm_int_eq xint (inject_term H)). intuition.
Qed.

Implicit Arguments PI_term_int_eq [t k].

(***********************************************************************)
(** polynomial associated to a rule *)

Require Export ATrs.
Require Export Max.

Definition rulePoly r :=
  let mvl := maxvar (lhs r) in
  let mvr := maxvar (rhs r) in
  let m := max mvl mvr in
    (pplus (pplus (termpoly (PI_poly PI) (inject_term (le_max_l mvl mvr)))
      (popp (termpoly (PI_poly PI) (inject_term (le_max_r mvl mvr)))))
    (popp (pconst (S m) 1))).

(***********************************************************************)
(** compatibility *)

Require Export ZUtil.

Lemma pi_compat_rule : forall r, coef_pos (rulePoly r) -> succ (lhs r) (rhs r).

Proof.
intros r H_coef_pos. unfold succ, IR. intro xint. unfold Dgt, Dlt, transp.
set (mvl := maxvar (lhs r)). set (mvr := maxvar (rhs r)).
set (m := max mvl mvr).
rewrite (PI_term_int_eq xint (le_max_l mvl mvr)).
rewrite (PI_term_int_eq xint (le_max_r mvl mvr)). do 2 rewrite val_peval_D.
pose (v := (Vmap (proj1_sig (P:=pos)) (fval xint (S (max mvl mvr))))).
apply pos_lt. rewrite <- (peval_const (1)%Z v). do 2 rewrite <- peval_minus.
unfold v. apply pos_peval. exact H_coef_pos.
Qed.

Require Export ACompat.

Lemma pi_compat : forall R,
  lforall (fun r => coef_pos (rulePoly r)) R -> compatible succ R.

Proof.
unfold compatible. intros. set (rho := mkRule l r).
change (succ (lhs rho) (rhs rho)). apply pi_compat_rule.
apply (lforall_in H H0).
Qed.

(***********************************************************************)
(** termination *)

Require Export AMannaNess.

Lemma polyInterpretationTermination : forall R,
  lforall (fun r => coef_pos (rulePoly r)) R -> WF (red R).

Proof.
intros R H. apply manna_ness with (succ := succ). apply pi_red_ord.
apply pi_compat. exact H.
Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac poly_int PI :=
  match goal with
    |- WF (red ?R) =>
      apply (polyInterpretationTermination PI R);
	compute; intuition; discriminate
  end.
