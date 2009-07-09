(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-22

semantic labelling (with ordered labels)
(Zantema, Fundamenta Informaticae, 1995, volume 24, pages 89-105)
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

(***********************************************************************)
(** ordering of labels *)

Variable Lgt : relation L. Infix ">L" := Lgt (at level 50).

Let Lge := Lgt %. Infix ">=L" := Lge (at level 50).

Definition Fun'_vars f a := Fun' (f,a) (fresh_vars (arity f)).

Definition decr f a b := mkRule (Fun'_vars f a) (Fun'_vars f b).

Definition Decr (rho : rule') :=
  exists f, exists a, exists b, a >L b /\ rho = decr f a b.

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
Definition unlab_rules := Frs HF.

Lemma Ft_epi : forall v t, unlab (lab v t) = t.

Proof.
intros v t. pattern t. apply term_ind with (Q := fun n (ts : terms n) =>
  Vmap (unlab o lab v) ts = ts); clear t; intros; simpl.
refl. apply args_eq. rewrite Vmap_map. rewrite H. apply Vcast_refl.
refl. rewrite H. rewrite H0. refl.
Qed.

Lemma Frs_iso : forall R, unlab_rules (lab_rules R) [=] R.

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

Lemma red_Frs_Decr : red (unlab_rules Decr) << @eq term.

Proof.
intros t u h. redtac. subst. destruct lr as [[l' r'] [h1 h2]].
destruct h1 as [f [a [b [ab h]]]]. inversion h. subst. inversion h2.
assert (HF (f,a) = HF (f,b)). apply UIP. apply eq_nat_dec. rewrite H. refl.
Qed.

Lemma rt_red_Frs_Decr : red (unlab_rules Decr) # << @eq term.

Proof.
intros t u. induction 1. apply red_Frs_Decr. hyp. refl. transitivity y; hyp.
Qed.

Lemma red_mod_Frs_Decr : forall E,
  red (unlab_rules (Decr ++ lab_rules E)) << red E %.

Proof.
intros E t u h. redtac. subst. apply Frs_app in lr. destruct lr.
left. eapply rt_red_Frs_Decr. apply rt_step. apply red_rule. hyp.
right. apply red_rule. do 2 destruct H. rewrite H0. clear H0. do 3 destruct H.
subst. destruct x0. simpl. repeat rewrite Ft_epi. hyp.
Qed.

Lemma rt_red_mod_Frs_Decr : forall E,
  red (unlab_rules (Decr ++ lab_rules E)) # << red E #.

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

Lemma hd_red_lab : forall v t u,
  hd_red R t u -> hd_red_mod Decr R' (lab v t) (lab v u).

Proof.
intros. redtac. subst. exists (lab v (sub s l)). split. apply rt_refl.
repeat rewrite lab_sub_eq. exists (lab (beta v s) l).
exists (lab (beta v s) r). exists (lab_sub v s). intuition.
exists (mkRule l r). exists (beta v s). intuition.
Qed.

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

Variable ge_compatE : forall l r, E (mkRule l r) -> l >=I r.
Variable ge_compatR : forall l r, R (mkRule l r) -> l >=I r.

Notation E' := (lab_rules E). Notation R' := (lab_rules R).

Lemma red_mod_lab : forall v t u,
  red_mod E R t u -> red_mod (Decr ++ E') R' (lab v t) (lab v u).

Proof.
intros. do 2 destruct H. ded (rt_red_lab ge_compatE v H).
ded (red_lab ge_compatR v H0). do 2 destruct H2. exists x0. intuition.
apply rt_trans with (lab v x).
eapply inclusion_elim. apply rt_red_mod_union. hyp.
eapply inclusion_elim. apply incl_rtc. apply red_incl. apply incl_appl. hyp.
Qed.

Lemma hd_red_mod_lab : forall v t u,
  hd_red_mod E R t u -> hd_red_mod (Decr ++ E') R' (lab v t) (lab v u).

Proof.
intros. do 2 destruct H. ded (rt_red_lab ge_compatE v H).
ded (hd_red_lab v H0). do 2 destruct H2. exists x0. intuition.
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

Lemma WF_hd_red_mod_lab :
  WF (hd_red_mod E R) <-> WF (hd_red_mod (Decr ++ E') R').

Proof.
split; intro.
(* -> *)
apply Fhd_red_mod_WF with (S2:=Sig) (F:=F) (HF:=HF).
apply WF_incl with (hd_red_mod E R). 2: hyp. intros t u h. destruct h.
destruct H0. apply rt_red_mod_Frs_Decr in H0. rewrite Frs_iso in H1.
exists x. auto.
(* <- *)
set (v := fun x : variable => some_elt I).
apply WF_incl with (Rof (hd_red_mod (Decr ++ E') R') (lab v)).
intros t u h. unfold Rof. apply hd_red_mod_lab. hyp.
apply WF_inverse. hyp.
Qed.

End red_mod.

(***********************************************************************)
(** enumeration of labelled rules for a finite domain *)

Section enum.

Variable Is : list I.
Variable Is_ok : forall x : I, In x Is.

Fixpoint enum_tuple n : list (vector I n) :=
  match n with
    | 0 => cons Vnil nil
    | S p => flat_map (fun ds => map (fun d => Vcons d ds) Is) (enum_tuple p)
  end.

Lemma enum_tuple_complete : forall n (ds : vector I n), In ds (enum_tuple n).

Proof.
induction n; simpl; intros. VOtac. auto. rewrite in_flat_map.
exists (Vtail ds). split. apply IHn.
set (f := fun d : I => Vcons d (Vtail ds)).
VSntac ds. change (In (f (Vhead ds)) (map f Is)). apply in_map. apply Is_ok.
Qed.

(*REMARK: define a more efficient function?
Fixpoint enum_tuple2 n : list (vector I n) :=
  match n with
    | 0 => nil
    | S p =>
      fold_left (fun e ds => fold_left (fun e d => Vcons d ds :: e) Is e)
      (enum_tuple2 p) nil
  end.*)

Definition enum R :=
  flat_map (fun ds => map (lab_rule (val_of_vec I ds)) R)
  (enum_tuple (S (maxvar_rules R))).

Lemma enum_correct : forall R a, In a (enum R) -> lab_rules (Rules R) a.

Proof.
intros. unfold enum in H. rewrite in_flat_map in H. do 2 destruct H.
rewrite in_map_iff in H0. do 2 destruct H0. exists x0. exists (val_of_vec I x).
intuition.
Qed.

Lemma enum_complete : forall R a, lab_rules (Rules R) a -> In a (enum R).

Proof.
intros. do 3 destruct H. set (n := maxvar_rules R).
unfold enum. rewrite in_flat_map. exists (vec_of_val x0 (S n)). split.
apply enum_tuple_complete. subst.
change (In (lab_rule x0 x) (map (lab_rule (fval x0 (S n))) R)).
rewrite map_lab_rule_fval. apply in_map. hyp. unfold n. omega.
Qed.

Infix "[=]" := equiv.

Lemma lab_rules_enum : forall R, lab_rules (Rules R) [=] Rules (enum R).

Proof.
split. apply enum_complete. apply enum_correct.
Qed.

(*REMARK: define a more efficient function?
Definition enum2 R :=
  let n := S (maxvar_rules R) in
    fold_left (fun e ds =>
      let v := val_of_vec I ds in
        fold_left (fun e (a : rule) => let (l,r) := a in
          mkRule (lab v l) (lab v r) :: e)
        R e)
    (enum_tuple n) nil.*)

(***********************************************************************)
(** enumeration of Decr rules *)

Variable Fs : list Sig.
Variable Fs_ok : forall x : Sig, In x Fs.

Variable Ls : list (L*L).
Variable Ls_ok : forall x y, x >L y <-> In (x,y) Ls.

Definition enum_Decr := flat_map (fun x : L*L =>
  let (a,b) := x in map (fun f => decr f a b) Fs) Ls.

Notation D' := enum_Decr.

Lemma enum_Decr_correct : forall x, In x D' -> Decr x.

Proof.
intros. unfold enum_Decr in H. rewrite in_flat_map in H.
destruct H as [[a b] [h1 h2]]. rewrite in_map_iff in h2.
destruct h2 as [f [h2 h3]]. exists f. exists a. exists b. split.
rewrite Ls_ok. hyp. auto.
Qed.

Lemma enum_Decr_complete : forall x, Decr x -> In x D'.

Proof.
intros. destruct H as [f [a [b [h]]]]. unfold enum_Decr. rewrite in_flat_map.
exists (a,b). split. rewrite <- Ls_ok. hyp. subst.
set (G := fun f => decr f a b). change (In (G f) (map G Fs)). apply in_map.
apply Fs_ok.
Qed.

Lemma Rules_enum_Decr : Rules D' [=] Decr.

Proof.
unfold equiv. split; intro. apply enum_Decr_correct. hyp.
apply enum_Decr_complete. hyp.
Qed.

(***********************************************************************)
(** main theorems (finite versions) *)

Require Import ATrs.

Variable bge : term->term->bool.
Variable bge_ok : rel bge << Ige.

Section bge.

Variable R : ATrs.rules Sig.
Variable bge_compat : forallb (brule bge) R = true.

Lemma ge_compat : forall l r, In (mkRule l r) R -> l >=I r.

Proof.
intros. apply bge_ok. unfold rel. change (brule bge (mkRule l r) = true).
rewrite forallb_forall in bge_compat. apply bge_compat. hyp.
Qed.

End bge.

Implicit Arguments ge_compat [R].

Section red_mod.

Variables E R : ATrs.rules Sig.

Notation E' := (enum E). Notation R' := (enum R).

Variable bge_compatE : forallb (brule bge) E = true.
Variable bge_compatR : forallb (brule bge) R = true.

Notation ge_compatE := (ge_compat bge_compatE).
Notation ge_compatR := (ge_compat bge_compatR).

Lemma WF_red_lab_fin : WF (red R) <-> WF (red_mod D' R').

Proof.
rewrite <- red_Rules. rewrite <- red_mod_Rules. rewrite WF_red_lab.
2: apply ge_compatR. apply WF_mor. rewrite Rules_enum_Decr.
rewrite lab_rules_enum. refl.
Qed.

Infix "++" := app.

Lemma WF_red_mod_lab_fin : WF (red_mod E R) <-> WF (red_mod (D' ++ E') R').

Proof.
repeat rewrite <- red_mod_Rules. rewrite WF_red_mod_lab.
2: apply ge_compatE. 2: apply ge_compatR.
apply WF_mor. rewrite Rules_app. rewrite Rules_enum_Decr.
repeat rewrite lab_rules_enum. refl.
Qed.

Lemma WF_hd_red_mod_lab_fin :
  WF (hd_red_mod E R) <-> WF (hd_red_mod (D' ++ E') R').

Proof.
repeat rewrite <- hd_red_mod_Rules. rewrite WF_hd_red_mod_lab.
2: apply ge_compatE. apply WF_mor. rewrite Rules_app. rewrite Rules_enum_Decr.
repeat rewrite lab_rules_enum. refl.
Qed.

End red_mod.

End enum.

End S.

Implicit Arguments lab_sig [Sig L beq].
Implicit Arguments Decr [Sig L beq].
Implicit Arguments lab_rules [Sig L beq I].
Implicit Arguments enum [Sig L beq I].
Implicit Arguments enum_Decr [Sig L beq].

(***********************************************************************)
(** module type for semantic labellings with unordered labels *)

Module Type SemLab.

  Parameter Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig).

  Require Export ARules. Notation rules := (rules Sig).

  Parameter I : interpretation Sig.

  Notation eqI := (IR I (@eq I)). Infix "=I" := eqI (at level 70).

  Variable beqI : term->term->bool.
  Variable beqI_ok : rel beqI << eqI.

  Parameter L : Type.
  Parameter beq : L -> L -> bool.
  Parameter beq_ok : forall l m, beq l m = true <-> l = m.

  Notation Sig' := (lab_sig beq_ok).

  Parameter pi : forall f : Sig, vector I (arity f) -> L.

  Notation lab_rules := (lab_rules beq_ok pi).

End SemLab.

(***********************************************************************)
(** module type for semantic labellings with ordered labels *)

Module Type OrdSemLab.

  Declare Module Export SL : SemLab.

  Parameter Lgt : relation L. Infix ">L" := Lgt (at level 50).

  Notation Lge := (Lgt %). Infix ">=L" := Lge (at level 50).

  Parameter Dge : relation I. Infix ">=D" := Dge (at level 50).

  Notation Ige := (IR I Dge). Infix ">=I" := Ige (at level 70).

  Variable bge : term->term->bool.
  Variable bge_ok : rel bge << Ige.

  Parameter pi_mon : forall f, Vmonotone (pi f) Dge Lge.
  Parameter I_mon : forall f, Vmonotone1 (fint I f) Dge.

  Notation Decr := (Decr beq_ok Lgt).

End OrdSemLab.

(***********************************************************************)
(** functor providing equality-ordered labels *)

Module Ord (Export S : SemLab) <: OrdSemLab.

  Module Export SL := S.

  Definition Lgt (_ _ : L) := False. Infix ">L" := Lgt (at level 50).

  Notation Lge := (Lgt %). Infix ">=L" := Lge (at level 50).

  Lemma Lge_is_eq : forall a b, a >=L b <-> a = b.

  Proof.
    firstorder.
  Qed.

  Definition Dge := @eq I.

  Definition bge := beqI.

  Definition bge_ok := beqI_ok.

  Lemma pi_mon : forall f, Vmonotone (pi f) Dge Lge.

  Proof.
    unfold Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    rewrite Lge_is_eq. rewrite H0. refl.
  Qed.

  Lemma I_mon : forall f, Vmonotone1 (fint I f) Dge.

  Proof.
    unfold Vmonotone1, Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    rewrite H0. refl.
  Qed.

End Ord.

(***********************************************************************)
(** module type for finite semantic labellings with unordered labels *)

Module Type FinSemLab.

  Declare Module Export SL : SemLab.

  Require Export ATrs. Notation rules := (rules Sig).

  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, In x Fs.

  Parameter Is : list I.
  Parameter Is_ok : forall x : I, In x Is.

  Notation lab_rules := (enum beq_ok pi Is).

End FinSemLab.

(***********************************************************************)
(** module type for finite semantic labellings with ordered labels *)

Module Type FinOrdSemLab.

  Declare Module Export OSL : OrdSemLab.

  Require Export ATrs. Notation rules := (rules Sig). Infix "++" := app.

  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, In x Fs.

  Parameter Is : list I.
  Parameter Is_ok : forall x : I, In x Is.

  Notation lab_rules := (enum beq_ok pi Is).

  Parameter Ls : list (L*L).
  Parameter Ls_ok : forall x y, x >L y <-> In (x,y) Ls.

  Notation Decr := (enum_Decr beq_ok Fs Ls).

End FinOrdSemLab.

(***********************************************************************)
(** functor providing equality-ordered labels *)

Module FinOrd (Export S : FinSemLab) <: FinOrdSemLab.

  Module Export OSL := Ord SL.

  Definition Lgt (_ _ : L) := False.

  Notation Lge := (Lgt %). Infix ">=L" := Lge (at level 50).

  Lemma Lge_is_eq : forall a b, a >=L b <-> a = b.

  Proof.
    firstorder.
  Qed.

  Definition Dge := @eq I.

  Lemma pi_mon : forall f, Vmonotone (pi f) Dge Lge.

  Proof.
    unfold Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    rewrite Lge_is_eq. rewrite H0. refl.
  Qed.

  Lemma I_mon : forall f, Vmonotone1 (fint I f) Dge.

  Proof.
    unfold Vmonotone1, Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    rewrite H0. refl.
  Qed.

  Definition Fs := Fs.
  Definition Fs_ok := Fs_ok.

  Definition Is := Is.
  Definition Is_ok := Is_ok.

  Definition Ls : list (L*L) := nil.

  Lemma Ls_ok : forall x y, x >L y <-> In (x,y) Ls.

  Proof.
    firstorder.
  Qed.

End FinOrd.

(***********************************************************************)
(** functor providing the properties of a semantic labelling
with ordered labels *)

Module OrdSemLabProps (Export L : OrdSemLab).

  Section S.

    Variables E R : rules.

    Variable ge_compatE : forall l r, E (mkRule l r) -> l >=I r.
    Variable ge_compatR : forall l r, R (mkRule l r) -> l >=I r.

    Lemma WF_red_mod_lab : WF (red_mod E R)
      <-> WF (red_mod (Decr ++ lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_red_mod_lab. refl. apply pi_mon. apply I_mon.
      apply ge_compatE. apply ge_compatR.
    Qed.

    Lemma WF_hd_red_mod_lab : WF (hd_red_mod E R)
      <-> WF (hd_red_mod (Decr ++ lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_hd_red_mod_lab. refl. apply pi_mon. apply I_mon.
      apply ge_compatE.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red_mod Decr (lab_rules R)).

    Proof.
      rewrite WF_red_lab. refl. apply pi_mon. apply I_mon. apply ge_compatR.
    Qed.

  End S.

End OrdSemLabProps.

(***********************************************************************)
(** functor providing the properties of a finite semantic labelling
with ordered labels *)

Module FinOrdSemLabProps (Export L : FinOrdSemLab).

  Section S.

    Variables E R : rules.

    Variable bge_compatE : forallb (brule bge) E = true.
    Variable bge_compatR : forallb (brule bge) R = true.

    Lemma WF_red_mod_lab : WF (red_mod E R)
      <-> WF (red_mod (Decr ++ lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_red_mod_lab_fin. refl. apply pi_mon. apply I_mon.
      apply Is_ok. apply Fs_ok. apply Ls_ok. apply bge_ok.
      apply bge_compatE. apply bge_compatR.
    Qed.

    Lemma WF_hd_red_mod_lab : WF (hd_red_mod E R)
      <-> WF (hd_red_mod (Decr ++ lab_rules E) (lab_rules R)).

    Proof.
      rewrite WF_hd_red_mod_lab_fin. refl. apply pi_mon. apply I_mon.
      apply Is_ok. apply Fs_ok. apply Ls_ok. apply bge_ok. apply bge_compatE.
    Qed.

    Lemma WF_red_lab : WF (red R) <-> WF (red_mod Decr (lab_rules R)).

    Proof.
      rewrite WF_red_lab_fin. refl. apply pi_mon. apply I_mon.
      apply Is_ok. apply Fs_ok. apply Ls_ok. apply bge_ok. apply bge_compatR.
    Qed.

  End S.

End FinOrdSemLabProps.

(***********************************************************************)
(** functor providing the properties of a semantic labelling
with unordered labels *)

Module SemLabProps (Export S : SemLab).
  Module OSL := Ord S.
  Include (OrdSemLabProps OSL).
End SemLabProps.

Module FinSemLabProps (Export S : FinSemLab).
  Module OSL := FinOrd S.
  Include (FinOrdSemLabProps OSL).
End FinSemLabProps.
