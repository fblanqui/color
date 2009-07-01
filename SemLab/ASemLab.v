(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-22

semantic labelling (with ordered labels)
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
Require Import SetUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (rules Sig).

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
Notation rule' := (ATrs.rule Sig'). Notation rules' := (rules Sig').

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

Definition lab_rules R a := exists b, exists v, R b /\ a = lab_rule v b.

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

Require Import VecMax.

Lemma lab_fval : forall v t n, n > maxvar t -> lab (fval v n) t = lab v t.

Proof.
intros v t. pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
  forall n, n > maxvars ts -> Vmap (lab v) ts = Vmap (lab (fval v n)) ts);
  clear t; simpl; intros.
(* Var *)
refl.
(* Fun *)
rewrite (H n). assert (Vmap (int v) v0 = Vmap (int (fval v n)) v0).
apply Vmap_eq. apply Vforall_intro. intros. apply term_int_eq_fval_lt.
apply le_lt_trans with (Vmax (Vmap (@maxvar Sig) v0)). apply Vmax_in.
apply Vin_map_intro. hyp. hyp. rewrite H1. refl. unfold maxvars. omega.
(* Vnil *)
refl.
(* Vcons *)
rewrite maxvars_cons in H1. rewrite gt_max in H1. destruct H1.
rewrite (H0 n0). 2: hyp. rewrite (H n0). 2: hyp. refl.
Qed.

Lemma lab_rule_fval : forall v a n,
  n > maxvar_rule a -> lab_rule (fval v n) a = lab_rule v a.

Proof.
intros v [l r] n. simpl. rewrite gt_max. intuition.
rewrite lab_fval. 2: hyp. rewrite lab_fval. 2: hyp. refl.
Qed.

(***********************************************************************)
(** ordering of labels *)

Variable Lgt : relation L. Infix ">L" := Lgt (at level 50).

Let Lge := Lgt %. Infix ">=L" := Lge (at level 50).

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

Lemma Ft_epi : forall v t, unlab (lab v t) = t.

Proof.
intros v t. pattern t. apply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (unlab o lab v) ts = ts); clear t; intros; simpl.
refl. apply args_eq. rewrite Vmap_map. rewrite H. apply Vcast_refl.
refl. rewrite H. rewrite H0. refl.
Qed.

Lemma Frs_iso : forall R : rules, Frs HF (lab_rules R) [=] R.

Proof.
intros R [l r]. split.
(* [= *)
intros [[l' r'] [h1 h2]]. destruct h1 as [[x y] [v [h h']]]. inversion h'.
inversion h2. subst. repeat rewrite Ft_epi. hyp.
(* =] *)
unfold Frs. intro. set (v := fun x : variable => some_elt I).
exists (mkRule (lab v l) (lab v r)). split.
unfold lab_rules. exists (mkRule l r). exists v. intuition.
simpl. repeat rewrite Ft_epi. refl.
Qed.

Lemma red_Frs_Decr : red (Frs HF Decr) << @eq term.

Proof.
intros t u h. redtac. subst. destruct lr as [[l' r'] [h1 h2]].
destruct h1 as [f [a [b [ab h]]]]. inversion h. subst. inversion h2.
assert (HF (f,a) = HF (f,b)). apply UIP. apply eq_nat_dec. rewrite H. refl.
Qed.

Lemma rt_red_Frs_Decr : red (Frs HF Decr) # << @eq term.

Proof.
intros t u. induction 1. apply red_Frs_Decr. hyp. refl. transitivity y; hyp.
Qed.

Lemma red_mod_Frs_Decr : forall E,
  red (Frs HF (Decr ++ lab_rules E)) << red E %.

Proof.
intros E t u h. redtac. subst. apply Frs_app in lr. destruct lr.
left. eapply rt_red_Frs_Decr. apply rt_step. apply red_rule. hyp.
right. apply red_rule. do 2 destruct H. rewrite H0. clear H0. do 3 destruct H.
subst. destruct x0. simpl. repeat rewrite Ft_epi. hyp.
Qed.

Lemma rt_red_mod_Frs_Decr : forall E,
  red (Frs HF (Decr ++ lab_rules E)) # << red E #.

Proof.
intro E. transitivity (red E % #). rewrite red_mod_Frs_Decr. refl.
rewrite rc_incl_rtc. rewrite rtc_invol. refl.
Qed.

(***********************************************************************)
(** main theorem *)

Variable Dge : relation I. Infix ">=D" := Dge (at level 50).

Let Ige := IR I Dge. Infix ">=I" := Ige (at level 70).

Variable pi_mon : forall f, Vmonotone (pi f) Dge Lge.
Variable I_mon : forall f, Vmonotone1 (fint I f) Dge.

Section red.

Variable R : rules. Notation R' := (lab_rules R).

Variable ge_compat : forall l r, R (mkRule l r) -> l >=I r.

Lemma red_lab : forall v t u,
  red R t u -> red_mod Decr R' (lab v t) (lab v u).

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

Lemma rt_red_lab : forall v t u,
  red R # t u -> red_mod Decr R' # (lab v t) (lab v u).

Proof.
induction 1. apply rt_step. apply red_lab. hyp. apply rt_refl.
apply rt_trans with (lab v y); hyp.
Qed.

Lemma WF_red_lab : WF (red R) <-> WF (red_mod Decr R').

Proof.
split; intro.
(* -> *)
apply Fred_mod_WF with (S2:=Sig) (F:=F) (HF:=HF). apply WF_incl with (red R).
2: hyp. intros t u h. redtac. ded (rt_red_Frs_Decr H0). subst t0. subst.
apply red_rule. eapply Frs_iso. hyp.
(* <- *)
set (v := fun x : variable => some_elt I).
apply WF_incl with (Rof (red_mod Decr R') (lab v)).
intros t u h. unfold Rof. apply red_lab. hyp.
apply WF_inverse. hyp.
Qed.

End red.

(***********************************************************************)
(** rewriting modulo *)

Section red_mod.

Variables E R : rules.
Notation E' := (lab_rules E). Notation R' := (lab_rules R).

Variable ge_compatE : forall l r, E (mkRule l r) -> l >=I r.
Variable ge_compatR : forall l r, R (mkRule l r) -> l >=I r.

Lemma red_mod_lab : forall v t u,
  red_mod E R t u -> red_mod (Decr ++ E') R' (lab v t) (lab v u).

Proof.
intros. do 2 destruct H. ded (rt_red_lab ge_compatE v H).
ded (red_lab ge_compatR v H0). do 2 destruct H2. exists x0. intuition.
apply rt_trans with (lab v x).
eapply inclusion_elim. apply rt_red_mod_union. hyp.
eapply inclusion_elim. apply incl_rtc. apply red_incl. apply incl_appl. hyp.
Qed.

Lemma WF_red_mod_lab : WF (red_mod E R) <-> WF (red_mod (Decr ++ E') R').

Proof.
split; intro.
(* -> *)
apply Fred_mod_WF with (S2:=Sig) (F:=F) (HF:=HF).
apply WF_incl with (red_mod E R). 2: hyp. intros t u h. destruct h.
destruct H0. apply rt_red_mod_Frs_Decr in H0. rewrite Frs_iso in H1.
exists x. auto.
(* <- *)
set (v := fun x : variable => some_elt I).
apply WF_incl with (Rof (red_mod (Decr ++ E') R') (lab v)).
intros t u h. unfold Rof. apply red_mod_lab. hyp.
apply WF_inverse. hyp.
Qed.

End red_mod.

(***********************************************************************)
(** enumeration of labelled rules for a finite domain *)

Section enum.

Require Import ListUtil.

Notation rules := (list rule).

Variable Is : list I.
Variable Is_ok : forall x : I, In x Is.

Fixpoint enum_tuple n : list (vector I n) :=
  match n with
    | 0 => cons Vnil nil
    | S p => flat_map (fun ds => map (fun d => Vcons d ds) Is) (enum_tuple p)
  end.

Lemma enum_tuple_complete : forall n (ds : vector I n), In ds (enum_tuple n).

Proof.
induction n; simpl; intros. VOtac. auto.
eapply In_flat_map_intro. apply (IHn (Vtail ds)).
set (f := fun d : I => Vcons d (Vtail ds)).
VSntac ds. change (In (f (Vhead ds)) (map f Is)). apply in_map. apply Is_ok.
Qed.

(*Fixpoint enum_tuple2 n : list (vector I n) :=
  match n with
    | 0 => nil
    | S p =>
      fold_left (fun e ds => fold_left (fun e d => Vcons d ds :: e) Is e)
      (enum_tuple2 p) nil
  end.*)

Definition enum R :=
  flat_map (fun ds => map (lab_rule (val_of_vec I ds)) R)
  (enum_tuple (S (maxvar_rules R))).

Notation fold_max := (@fold_max Sig).

Require Import Max.

Lemma map_lab_rule_fval : forall v R n,
  n > maxvar_rules R -> map (lab_rule (fval v n)) R = map (lab_rule v) R.

Proof.
induction R; simpl; intros. refl. unfold maxvar_rules in H. simpl in H.
rewrite lab_rule_fval. rewrite IHR. refl.
apply le_lt_trans with (fold_left fold_max R (fold_max 0 a)).
apply maxvar_rules_init_mon. apply le_max_l. hyp.
apply le_lt_trans with (fold_left fold_max R (fold_max 0 a)).
apply maxvar_rules_init. hyp.
Qed.

Lemma enum_complete : forall R a, lab_rules (Rules R) a -> In a (enum R).

Proof.
induction R.
(* nil *)
firstorder.
(* cons *)
intros. do 3 destruct H. set (n := maxvar_rules (a::R)).
apply In_flat_map_intro with (y := vec_of_val x0 (S n)).
  apply enum_tuple_complete.
subst. change (In (lab_rule x0 x) (map (lab_rule (fval x0 (S n))) (a::R))).
rewrite map_lab_rule_fval. apply in_map. hyp. unfold n. omega.
Qed.

(*Definition enum2 R :=
  let n := maxvar_rules R in
    fold_left (fun e ds =>
      let v := val_of_vec I ds in
        fold_left (fun e (a : rule) => let (l,r) := a in
          mkRule (lab v l) (lab v r) :: e)
        R e)
    (enum_tuple n) nil.*)

End enum.

End S.
