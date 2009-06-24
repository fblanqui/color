(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-22

semantic labelling
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import AInterpretation.
Require Import BoolUtil.
Require Import LogicUtil.
Require Import EqUtil.
Require Import VecUtil.
Require Import List.
Require Import SN.
Require Import RelUtil.
Require Import AWFMInterpretation.
Require Import NaryFunction.
Require Import NatUtil.
Require Import ARelation.
Require Import ARules.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** labels *)

Variable L : Type.
Variable beq : L -> L -> bool.
Variable beq_ok : forall l m, beq l m = true <-> l = m.

(***********************************************************************)
(** labelled signature *)

Definition lab_symb := (Sig * L)%type.

Definition beq_lab_symb (fl1 fl2 : lab_symb) :=
  let (f1,l1) := fl1 in let (f2,l2) := fl2 in beq_symb f1 f2 && beq l1 l2.

Lemma beq_lab_symb_ok : forall fl1 fl2,
  beq_lab_symb fl1 fl2 = true <-> fl1 = fl2.

Proof.
intros [f1 l1] [f2 l2]. simpl. split; intro. rewrite andb_eq in H. destruct H.
rewrite beq_symb_ok in H. rewrite beq_ok in H0. subst. refl.
inversion H. subst. rewrite andb_eq. rewrite (beq_refl beq_ok).
rewrite (beq_refl (@beq_symb_ok Sig)). auto.
Qed.

Definition lab_arity (fl : lab_symb) := let (f,_) := fl in arity f.

Definition lab_sig := mkSignature lab_arity beq_lab_symb_ok.

Notation Sig' := lab_sig. Notation Fun' := (@Fun Sig').
Notation term' := (ATerm.term Sig'). Notation terms' := (vector term').
Notation rule' := (ATrs.rule Sig'). Notation rules' := (list rule').

(***********************************************************************)
(** labelling *)

Variable I : interpretation Sig.

Notation int := (@term_int _ I).

Variable pi : forall f : Sig, vector I (arity f) -> L.

Fixpoint lab v t :=
  match t with
    | Var x => Var x
    | Fun f ts => Fun' (f, pi f (Vmap (int v) ts)) (Vmap (lab v) ts)
  end.

Definition lab_rule v (a : rule) :=
  let (l,r) := a in mkRule (lab v l) (lab v r).

Definition lab_sub v s (x : variable) := lab v (s x).

Notation "f 'o' g" := (fun x => f (g x)) (at level 70).

Lemma lab_sub_eq : forall v s t,
  lab v (sub s t) = sub (lab_sub v s) (lab (beta v s) t).

Proof.
intros v s t. pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (lab v o sub s) ts = Vmap (sub (lab_sub v s) o lab (beta v s)) ts);
  clear t; intros; simpl.
(* Var *)
unfold lab_sub. refl.
(* Fun *)
repeat rewrite Vmap_map. rewrite Vmap_eq_ext with (g := int (beta v s)).
2: apply substitution_lemma. apply args_eq. hyp.
(* Vnil *)
refl.
(* Vcons *)
apply Vcons_eq_intro; hyp.
Qed.

(***********************************************************************)
(** ordering of labels *)

Variable Lgt : relation L.
Infix ">L" := Lgt (at level 50).

Definition Lge := Lgt %.
Infix ">=L" := Lge (at level 50).

Fixpoint fresh_vars x k :=
  match k as k return terms' k with
    | 0 => Vnil
    | S l => Vcons (Var x) (fresh_vars (S x) l)
  end.

Lemma Vnth_fresh_vars : forall k i (h : i<k) x,
  Vnth (fresh_vars x k) h = Var (x+i).

Proof.
induction k; simpl; intros. absurd_arith. destruct i.
apply (f_equal (@Var _)). omega.
rewrite IHk. apply (f_equal (@Var _)). omega.
Qed.

Notation fvars := (fresh_vars 0).

Definition Fun'_vars f a := Fun' (f,a) (fvars (arity f)).

Definition decr f a b := mkRule (Fun'_vars f a) (Fun'_vars f b).

Definition Decr (rho : rule') :=
  exists f, exists a, exists b, a >L b /\ rho = decr f a b.

Definition sub_vars n (ts :terms' n) x : term' :=
  match lt_ge_dec x n with
    | left h => Vnth ts h
    | _ => Var x
  end.

Lemma sub_fresh_vars : forall n (ts : terms' n),
  ts = Vmap (sub (sub_vars ts)) (fvars n).

Proof.
intros. apply Veq_nth. intros. rewrite Vnth_map.
rewrite Vnth_fresh_vars. simpl. unfold sub_vars.
case (lt_ge_dec i n); intro. apply Vnth_eq. refl. absurd_arith.
Qed.

Lemma Lge_Decr : forall f (ts : terms' (arity f)) a b,
  a >=L b -> red Decr # (Fun' (f,a) ts) (Fun' (f,b) ts).

Proof.
intros. destruct H. subst. apply rt_refl. apply rt_step.
exists (Fun'_vars f a). exists (Fun'_vars f b). exists Hole.
exists (sub_vars ts). simpl. intuition.
exists f. exists a. exists b. intuition.
apply args_eq. apply sub_fresh_vars.
apply args_eq. apply sub_fresh_vars.
Qed.

(***********************************************************************)
(** unlabelling *)

Require Import AMorphism.

Definition F (f' : Sig') := let (f,_) := f' in f.

Lemma HF : forall f', arity f' = arity (F f').

Proof.
intros (f,l). refl.
Qed.

Definition unlab := Ft HF.

Lemma unlab_lab : forall v t, unlab (lab v t) = t.

Proof.
intros v t. pattern t. apply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (unlab o lab v) ts = ts); clear t; intros; simpl.
refl. apply args_eq. rewrite Vmap_map. rewrite H. apply Vcast_refl.
refl. rewrite H. rewrite H0. refl.
Qed.

Lemma red_Frs_Decr_eq : red (Frs HF Decr) << @eq term.

Proof.
intros t u h. redtac. subst. destruct lr as [[l' r'] [h1 h2]].
destruct h1 as [f [a [b [ab h]]]]. inversion h. subst. inversion h2.
assert (HF (f,a) = HF (f,b)). apply UIP. apply eq_nat_dec. rewrite H. refl.
Qed.

Lemma rt_red_Frs_Decr_eq : red (Frs HF Decr) # << @eq term.

Proof.
intros t u. induction 1. apply red_Frs_Decr_eq. hyp. refl. transitivity y; hyp.
Qed.

(***********************************************************************)
(** main theorem *)

Variable R : rule -> Prop.

Definition lab_rules a := exists b, exists v, R b /\ a = lab_rule v b.

Notation R' := lab_rules.

Lemma Frs_incl : incl (Frs HF R') R.

Proof.
intros [l r h]. destruct h as [[l' r'] [h1 h2]].
destruct h1 as [[x y] [v [h h']]]. inversion h'. inversion h2. subst.
repeat rewrite unlab_lab. hyp.
Qed.

Variable Dge : relation I.
Infix ">=D" := Dge (at level 50).

Definition ge := IR I Dge.
Infix ">=" := ge.

Variable ge_compat : forall l r, R (mkRule l r) -> l >= r.

Variable pi_mon : forall f, Vmonotone (pi f) Dge Lge.

Variable I_mon : forall f, Vmonotone1 (fint I f) Dge.

Lemma red_lab : forall v t u,
  red R t u -> (red_mod Decr R') (lab v t) (lab v u).

Proof.
intros. redtac. subst. elim c; clear c.
(* Hole *)
simpl. exists (lab v (sub s l)). split. apply rt_refl.
repeat rewrite lab_sub_eq. exists (lab (beta v s) l).
exists (lab (beta v s) r). exists Hole. exists (lab_sub v s). intuition.
exists (mkRule l r). exists (beta v s). intuition.
(* Cont *)
intros. simpl. repeat rewrite Vmap_cast. repeat rewrite Vmap_app. simpl.
set (v0' := Vmap (int v) v0). set (t := fill c (sub s l)). fold t in H.
set (v1' := Vmap (int v) v1). set (u := fill c (sub s r)). fold u in H.
assert (int v t >=D int v u). assert (IR I Dge t u).
apply IR_context_closed. hyp. apply IR_substitution_closed. apply ge_compat.
hyp. apply H0.
set (a := pi f (Vcast (Vapp v0' (Vcons (int v t) v1')) e)).
set (b := pi f (Vcast (Vapp v0' (Vcons (int v u) v1')) e)).
assert (a >=L b). apply pi_mon. hyp.
set (w0 := Vmap (lab v) v0). set (w1 := Vmap (lab v) v1).
set (ts := Vcast (Vapp w0 (Vcons (lab v t) w1)) e). ded (Lge_Decr f ts H1).
set (us := Vcast (Vapp w0 (Vcons (lab v u) w1)) e).
do 2 destruct H. set (vs := Vcast (Vapp w0 (Vcons x w1)) e).
exists (Fun' (f,b) vs). split. apply rt_trans with (Fun' (f,b) ts). hyp.
apply context_closed_fun with (R := red Decr #).
apply context_closed_rtc. apply context_closed_red. hyp.
apply context_closed_fun with (R := red R'). apply context_closed_red. hyp.
Qed.

Lemma WF_lab : WF (red R) <-> WF (red_mod Decr R').

Proof.
split; intro.
(* -> *)
apply Fred_mod_WF with (S2:=Sig) (F:=F) (HF:=HF). apply WF_incl with (red R).
2: hyp. intros t u h. redtac. ded (rt_red_Frs_Decr_eq H0). subst t0. subst.
apply red_rule. apply Frs_incl. hyp.
(* <- *)
set (v := fun x : variable => some_elt I).
apply WF_incl with (Rof (red_mod Decr R') (lab v)).
intros t u h. unfold Rof. apply red_lab. hyp.
apply WF_inverse. hyp.
Qed.

End S.
