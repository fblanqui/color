(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

from algebraic terms to varyadic terms
************************************************************************)

(* $Id: VTerm_of_ATerm.v,v 1.1.1.1 2006-09-08 09:06:59 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

(***********************************************************************)
(* algebraic signature *)

Variable ASig : Signature.

Require Export ATerm.

Notation aterm := (term ASig).
Notation aterms := (vector aterm).
Notation AFun := (@Fun ASig).
Notation "'args' f" := (aterms (arity f)) (at level 70).

(***********************************************************************)
(* corresponding varyadic signature *)

Require Export VSignature.

Definition VSig_of_ASig := mkSignature (@ASignature.eq_symb_dec ASig).

Notation VSig := VSig_of_ASig.

Require Export VTerm.

Notation vterm := (term VSig).
Notation vterms := (list vterm).
Notation VFun := (@Fun VSig).

(***********************************************************************)
(* conversion of terms *)

Fixpoint vterm_of_aterm (t : aterm) : vterm :=
  match t with
    | ATerm.Var x => Var x
    | ATerm.Fun f v =>
      let fix vterms_of_aterms n (ts : aterms n) {struct ts} : vterms :=
	match ts with
	  | Vnil => nil
	  | Vcons t' n' ts' => vterm_of_aterm t' :: vterms_of_aterms n' ts'
	end
	in VFun f (vterms_of_aterms (arity f) v)
  end.

Fixpoint vterms_of_aterms n (ts : aterms n) {struct ts} : vterms :=
  match ts with
    | Vnil => nil
    | Vcons t' _ ts' => vterm_of_aterm t' :: vterms_of_aterms ts'
  end.

Lemma vterm_fun : forall f (ts : args f),
  vterm_of_aterm (AFun f ts) = VFun f (vterms_of_aterms ts).

Proof.
intros. simpl. apply (f_equal (VFun f)). generalize dependent (arity f). induction ts; simpl; auto.
Qed.

Lemma vterms_cast : forall n (ts : aterms n) m (h : n=m),
  vterms_of_aterms (Vcast ts h) = vterms_of_aterms ts.

Proof.
induction ts; intros; destruct m; try (refl || discriminate). simpl.
apply (f_equal (cons (vterm_of_aterm a))). apply IHts.
Qed.

Lemma vterms_app : forall n1 (ts1 : aterms n1) n2 (ts2 : aterms n2),
  vterms_of_aterms (Vapp ts1 ts2) = vterms_of_aterms ts1 ++ vterms_of_aterms ts2.

Proof.
induction ts1; simpl. refl. intros. apply (f_equal (cons (vterm_of_aterm a))). apply IHts1.
Qed.

Lemma vterms_map : forall (A : Set) (f : A -> aterm) n (v : vector A n),
  vterms_of_aterms (Vmap f v) = map (fun x => vterm_of_aterm (f x)) (list_of_vec v).

Proof.
induction v; simpl. refl. apply (f_equal (cons (vterm_of_aterm (f a)))). apply IHv.
Qed.

(***********************************************************************)
(* conversion of contexts *)

Require Export AContext.

Notation acont := (@context ASig).
Notation ACont := (@Cont ASig).
Notation afill := fill.

Require Export VContext.

Notation vcont := (@context VSig).
Notation VCont := (@Cont VSig).

Fixpoint vcont_of_acont (c : acont) : vcont :=
  match c with
    | AContext.Hole => Hole
    | AContext.Cont f i j _ ts1 d ts2 =>
      VCont f (vterms_of_aterms ts1) (vcont_of_acont d) (vterms_of_aterms ts2)
  end.

Lemma vterm_fill : forall t c,
  vterm_of_aterm (afill c t) = fill (vcont_of_acont c) (vterm_of_aterm t).

Proof.
induction c. refl. simpl afill. rewrite vterm_fun. rewrite vterms_cast. rewrite vterms_app.
simpl. apply (f_equal (VFun f)). apply (f_equal (app (vterms_of_aterms v))). rewrite IHc. refl.
Qed.

(***********************************************************************)
(* conversion of substitutions *)

Require Export ASubstitution.

Notation asubs := (@substitution ASig).
Notation aapp := (@app ASig).

Require Export VSubstitution.

Notation vsubs := (@substitution VSig).
Notation vapp := (@app VSig).

Definition vsubs_of_asubs (s : asubs) x := vterm_of_aterm (s x).

Lemma vterm_subs : forall s t,
  vterm_of_aterm (aapp s t) = vapp (vsubs_of_asubs s) (vterm_of_aterm t).

Proof.
intros. pattern t. apply ATerm.term_ind with (Q := fun n (ts : aterms n) =>
  vterms_of_aterms (Vmap (aapp s) ts) = map (vapp (vsubs_of_asubs s)) (vterms_of_aterms ts)).
refl. intros. rewrite ASubstitution.app_fun. do 2 rewrite vterm_fun. rewrite app_fun.
apply (f_equal (VFun f)). exact H. refl. intros. simpl. rewrite H.
apply (f_equal (cons (vapp (vsubs_of_asubs s) (vterm_of_aterm t0)))). exact H0.
Qed.

(***********************************************************************)
(* conversion of rules *)

Require Export ATrs.

Notation arule := (@ATrs.rule ASig).
Notation ared := (@ATrs.red ASig).

Require Export VTrs.

Notation vrule := (@VTrs.rule VSig).
Notation vred := (@VTrs.red VSig).

Definition vrule_of_arule (rho : arule) : vrule :=
  let (l,r) := rho in mkRule (vterm_of_aterm l) (vterm_of_aterm r).

Variable R : list arule.

Definition vrules_of_arules := map vrule_of_arule R.

Notation S := vrules_of_arules.

Lemma vred_of_ared : forall t u, ared R t u -> vred S (vterm_of_aterm t) (vterm_of_aterm u).

Proof.
intros. ATrs.redtac. subst t. subst u. do 2 rewrite vterm_fill. do 2 rewrite vterm_subs.
apply red_rule. change (In (vrule_of_arule (ATrs.mkRule l r)) S). unfold S. apply in_map. exact H.
Qed.

(***********************************************************************)
(* preservation of termination *)

Require Export WfUtil.

Lemma Acc_vred_imp_Acc_ared : forall t,
  sn (vred S) t -> forall u, t = vterm_of_aterm u -> sn (ared R) u.

Proof.
induction 1. intros. subst x. apply Acc_intro. intros. apply (H0 (vterm_of_aterm y)).
unfold transp. apply vred_of_ared. exact H1. refl.
Qed.

Lemma wf_vred_imp_wf_ared : wf (vred S) -> wf (ared R).

Proof.
intro. unfold well_founded. intro. eapply Acc_vred_imp_Acc_ared. apply H. refl.
Qed.

End S.